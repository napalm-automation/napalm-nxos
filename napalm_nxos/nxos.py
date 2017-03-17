# -*- coding: utf-8 -*-
# Copyright 2015 Spotify AB. All rights reserved.
#
# The contents of this file are licensed under the Apache License, Version 2.0
# (the "License"); you may not use this file except in compliance with the
# License. You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations under
# the License.

from __future__ import unicode_literals

# import stdlib
import re
import os
import json
import time
import uuid
import tempfile
from scp import SCPClient
import paramiko
import hashlib
from datetime import datetime
from requests.exceptions import ConnectionError

# import third party lib
from netaddr import IPAddress
from netaddr.core import AddrFormatError

from pynxos.device import Device as NXOSDevice
from pynxos.features.file_copy import FileTransferError as NXOSFileTransferError
from pynxos.features.file_copy import FileCopy
from pynxos.errors import CLIError

from netmiko import ConnectHandler
from netmiko.ssh_exception import NetMikoTimeoutException

# import NAPALM Base
import napalm_base.helpers
from napalm_base import NetworkDriver
from napalm_base.utils import py23_compat
from napalm_base.exceptions import ConnectionException
from napalm_base.exceptions import MergeConfigException
from napalm_base.exceptions import CommandErrorException
from napalm_base.exceptions import ReplaceConfigException
import napalm_base.constants as c

UPTIME_KEY_MAP = {
    'kern_uptm_days': 'up_days',
    'kern_uptm_hrs': 'up_hours',
    'kern_uptm_mins': 'up_mins',
    'kern_uptm_secs': 'up_secs'
}


class NXOSDriver(NetworkDriver):
    def __init__(self, hostname, username, password, timeout=60, optional_args=None):
        if optional_args is None:
            optional_args = {}
        self.hostname = hostname
        self.username = username
        self.password = password
        self.timeout = timeout
        self.up = False
        self.replace = True
        self.loaded = False
        self.fc = None
        self.changed = False
        self.replace_file = None
        self.merge_candidate = ''
        self.ssh_connection = False

        if optional_args is None:
            optional_args = {}

        self.transport = optional_args.get('nxos_protocol', 'http')

        if self.transport == 'https':
            self.port = optional_args.get('port', 443)
        elif self.transport == 'http':
            self.port = optional_args.get('port', 80)
        elif self.transport == 'netmiko_nxos':
            # Netmiko possible arguments
            netmiko_argument_map = {
                'port': None,
                'verbose': False,
                'timeout': self.timeout,
                'global_delay_factor': 1,
                'use_keys': False,
                'key_file': None,
                'ssh_strict': False,
                'system_host_keys': False,
                'alt_host_keys': False,
                'alt_key_file': '',
                'ssh_config_file': None,
                'allow_agent': False
            }

            # Build dict of any optional Netmiko args
            self.netmiko_optional_args = {
                k: optional_args.get(k, v)
                for k, v in netmiko_argument_map.items()
            }

            self.port = optional_args.get('port', 22)
            self.sudo_pwd = optional_args.get('sudo_pwd', self.password)

    def _open_ssh_session(self):
        try:
            self.device = ConnectHandler(device_type='cisco_nxos',
                                         host=self.hostname,
                                         username=self.username,
                                         password=self.password,
                                         **self.netmiko_optional_args)
            self.ssh_connection = True
            self.device.enable()
        except NetMikoTimeoutException:
            raise ConnectionException('Cannot connect to {}'.format(self.hostname))

    def _open_nxapi_session(self):
        try:
            self.device = NXOSDevice(self.hostname,
                                     self.username,
                                     self.password,
                                     timeout=self.timeout,
                                     port=self.port,
                                     transport=self.transport)
            self.device.show('show hostname')
            self.up = True
        except (CLIError, ValueError):
            # unable to open connection
            raise ConnectionException('Cannot connect to {}'.format(self.hostname))

    def open(self):
        if self.transport == 'netmiko_nxos':
            self._open_ssh_session()
        else:
            self._open_nxapi_session()

    def _close_ssh_session(self):
        self.device.disconnect()

    def close(self):
        if self.changed:
            self._delete_file(self.backup_file)
        if self.ssh_connection:
            self._close_ssh_session()
        self.device = None

    @staticmethod
    def _compute_timestamp(stupid_cisco_output):
        """
        Some fields such `uptime` are returned as: 23week(s) 3day(s)
        This method will determine the epoch of the event.
        e.g.: 23week(s) 3day(s) -> 1462248287
        """
        if not stupid_cisco_output or stupid_cisco_output == 'never':
            return -1.0

        things = {
            'second(s)': {
                'weight': 1
            },
            'minute(s)': {
                'weight': 60
            },
            'hour(s)': {
                'weight': 3600
            },
            'day(s)': {
                'weight': 24 * 3600
            },
            'week(s)': {
                'weight': 7 * 24 * 3600
            },
            'year(s)': {
                'weight': 365.25 * 24 * 3600
            }
        }

        things_keys = things.keys()
        for part in stupid_cisco_output.split():
            for key in things_keys:
                if key in part:
                    things[key]['count'] = napalm_base.helpers.convert(
                        int, part.replace(key, ''), 0)

        delta = sum([det.get('count', 0) * det.get('weight') for det in things.values()])
        return time.time() - delta

    @staticmethod
    def _get_reply_body(result):
        # useful for debugging
        ret = result.get('ins_api', {}).get('outputs', {}).get('output', {}).get('body', {})
        # Original 'body' entry may have been an empty string, don't return that.
        if not isinstance(ret, dict):
            return {}
        return ret

    @staticmethod
    def _get_table_rows(parent_table, table_name, row_name):
        # because if an inconsistent piece of shit.
        # {'TABLE_intf': [{'ROW_intf': {
        # vs
        # {'TABLE_mac_address': {'ROW_mac_address': [{
        # vs
        # {'TABLE_vrf': {'ROW_vrf': {'TABLE_adj': {'ROW_adj': {
        _table = parent_table.get(table_name)
        _table_rows = []
        if isinstance(_table, list):
            _table_rows = [_table_row.get(row_name) for _table_row in _table]
        elif isinstance(_table, dict):
            _table_rows = _table.get(row_name)
        if not isinstance(_table_rows, list):
            _table_rows = [_table_rows]
        return _table_rows

    @staticmethod
    def fix_checkpoint_string(string, filename):
        # used to generate checkpoint-like files
        pattern = '''!Command: Checkpoint cmd vdc 1'''

        if '!Command' in string:
            return re.sub('!Command.*', pattern.format(filename), string)
        else:
            return "{0}\n{1}".format(pattern.format(filename), string)

    def _get_reply_table(self, result, table_name, row_name):
        return self._get_table_rows(result, table_name, row_name)

    def _get_command_table(self, command, table_name, row_name):
        if self.ssh_connection:
            command += ' | json'
            try:
                json_output = json.loads(self.device.send_command(command))
            except ValueError:
                return {}
        else:
            json_output = self.device.show(command)
        return self._get_reply_table(json_output, table_name, row_name)

    def is_alive(self):
        if self.ssh_connection:
            return {
                'is_alive': self.device.remote_conn.transport.is_active()
                }
        else:
            if self.device:
                return {'is_alive': True}
            else:
                return {'is_alive': False}

    def load_replace_candidate(self, filename=None, config=None):
        if self.ssh_connection:
            self._replace_candidate_ssh(filename, config)
        else:
            self._replace_candidate(filename, config)
        self.replace = True
        self.loaded = True

    def _get_flash_size(self):
        command = 'dir {}'.format('bootflash:')
        output = self.device.send_command(command)

        match = re.search(r'(\d+) bytes free', output)
        bytes_free = match.group(1)

        return int(bytes_free)

    def _enough_space(self, filename):
        flash_size = self._get_flash_size()
        file_size = os.path.getsize(filename)
        if file_size > flash_size:
            return False
        return True

    def _verify_remote_file_exists(self, dst, file_system='bootflash:'):
        command = 'dir {0}/{1}'.format(file_system, dst)
        response = self.device.send_command(command)
        if 'No such file' in response:
            raise ReplaceConfigException('Could not transfer file.')

    def _replace_candidate_ssh(self, filename, config):
        if not filename:
            file_content = self.fix_checkpoint_string(config, self.replace_file)
            filename = self._create_tmp_file(config)
        else:
            if not os.path.isfile(filename):
                raise ReplaceConfigException("File {} not found".format(filename))

        self.replace_file = filename
        with open(self.replace_file, 'r+') as f:
            file_content = f.read()
            file_content = self.fix_checkpoint_string(file_content, self.replace_file)
            f.write(file_content)

        if not self._enough_space(self.replace_file):
            msg = 'Could not transfer file. Not enough space on device.'
            raise ReplaceConfigException(msg)

        self._check_file_exists(self.replace_file)
        dest = os.path.basename(self.replace_file)
        full_remote_path = 'bootflash:{}'.format(dest)
        with paramiko.SSHClient() as ssh:
            ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
            ssh.connect(hostname=self.hostname, username=self.username, password=self.password)

            try:
                with SCPClient(ssh.get_transport()) as scp_client:
                    scp_client.put(self.replace_file, full_remote_path)
            except Exception:
                time.sleep(10)
                file_size = os.path.getsize(filename)
                temp_size = self._verify_remote_file_exists(dest)
                if int(temp_size) != int(file_size):
                    msg = ('Could not transfer file. There was an error '
                           'during transfer. Please make sure remote '
                           'permissions are set.')
                raise ReplaceConfigException(msg)
        self.config_replace = True
        if config and os.path.isfile(self.replace_file):
            os.remove(self.replace_file)

    def _file_already_exists(self, dst):
        dst_hash = self._get_remote_md5(dst)
        src_hash = self._get_local_md5(dst)
        if src_hash == dst_hash:
            return True
        return False

    def _check_file_exists(self, cfg_file):
        cmd = 'dir {}'.format(cfg_file)
        output = self.device.send_command(cmd)
        if 'No such file' in output:
            return False
        else:
            return self._file_already_exists(cfg_file)

    def _get_remote_md5(self, dst):
        command = 'show file {0} md5sum'.format(dst)
        return self.device.send_command(command).strip()

    def _get_local_md5(self, dst, blocksize=2**20):
        md5 = hashlib.md5()
        local_file = open(dst, 'rb')
        buf = local_file.read(blocksize)
        while buf:
            md5.update(buf)
            buf = local_file.read(blocksize)
        local_file.close()
        return md5.hexdigest()

    def _replace_candidate(self, filename, config):
        if not filename and not config:
            raise ReplaceConfigException('filename or config param must be provided.')

        if filename is None:
            temp_file = tempfile.NamedTemporaryFile()
            temp_file.write(config)
            temp_file.flush()
            cfg_filename = temp_file.name
        else:
            cfg_filename = filename

        self.replace_file = cfg_filename

        with open(self.replace_file, 'r') as f:
            file_content = f.read()

        file_content = self.fix_checkpoint_string(file_content, self.replace_file)
        temp_file = tempfile.NamedTemporaryFile()
        temp_file.write(file_content)
        temp_file.flush()
        self.replace_file = cfg_filename

        self._send_file_api(temp_file.name, cfg_filename)

    def load_merge_candidate(self, filename=None, config=None):
        self.replace = False
        self.loaded = True

        if not filename and not config:
            raise MergeConfigException('filename or config param must be provided.')

        self.merge_candidate += '\n'  # insert one extra line
        if filename is not None:
            with open(filename, "r") as f:
                self.merge_candidate += f.read()
        else:
            self.merge_candidate += config

    def _send_file_api(self, filename, dest):
        self.fc = FileCopy(self.device, filename, dst=dest.split('/')[-1])
        try:
            if not self.fc.remote_file_exists():
                self.fc.send()
            elif not self.fc.file_already_exists():
                self.fc.send()
        except NXOSFileTransferError as fte:
            raise ReplaceConfigException(fte.message)

    @staticmethod
    def _create_tmp_file(config):
        tmp_dir = tempfile.gettempdir()
        rand_fname = py23_compat.text_type(uuid.uuid4())
        filename = os.path.join(tmp_dir, rand_fname)
        with open(filename, 'wt') as fobj:
            fobj.write(config)
        return filename

    def _create_sot_file(self):
        """Create Source of Truth file to compare."""
        commands = ['terminal dont-ask', 'checkpoint file sot_file']
        self._send_config_commands(commands)

    def _get_diff(self):
        """Get a diff between running config and a proposed file."""
        diff = []
        self._create_sot_file()
        command = ('show diff rollback-patch file {0} file {1}'.format(
                   'sot_file', self.replace_file.split('/')[-1]))
        diff_out = self._send_command(command, fmt='text')
        try:
            diff_out = diff_out.split(
                '#Generating Rollback Patch')[1].replace(
                    'Rollback Patch is Empty', '').strip()
            for line in diff_out.splitlines():
                if line:
                    if line[0].strip() != '!':
                        diff.append(line.rstrip(' '))
        except (AttributeError, KeyError):
            raise ReplaceConfigException(
                'Could not calculate diff. It\'s possible the given file doesn\'t exist.')
        return '\n'.join(diff)

    def _get_merge_diff(self):
        diff = []
        running_config = self.get_config(retrieve='running')['running']
        running_lines = running_config.splitlines()
        for line in self.merge_candidate.splitlines():
            if line not in running_lines and line:
                if line[0].strip() != '!':
                    diff.append(line)
        return '\n'.join(diff)
        # the merge diff is not necessarily what needs to be loaded
        # for example under NTP, as the `ntp commit` command might be
        # alread configured, it is mandatory to be sent
        # otherwise it won't take the new configuration - see #59
        # https://github.com/napalm-automation/napalm-nxos/issues/59
        # therefore this method will return the real diff
        # but the merge_candidate will remain unchanged
        # previously: self.merge_candidate = '\n'.join(diff)

    def compare_config(self):
        if self.loaded:
            if not self.replace:
                return self._get_merge_diff()
                # return self.merge_candidate
            diff = self._get_diff()
            return diff
        return ''

    def _save_ssh(self, filename='startup-config'):
        output = self.device.send_command('copy run %s' % filename)
        if 'complete' in output.lower():
            return True
        return False

    def _commit_merge(self):
        commands = [command for command in self.merge_candidate.splitlines() if command]
        if self.ssh_connection:
            self.device.send_config_set(commands)
            if not self._save_ssh():
                raise CommandErrorException('Unable to commit config!')
        else:
            self.device.config_list(commands)
            if not self.device.save():
                raise CommandErrorException('Unable to commit config!')

    def _save_config(self, filename):
        """Save the current running config to the given file."""
        if self.ssh_connection:
            self.device.send_command('checkpoint file {}'.format(filename))
        else:
            self.device.show('checkpoint file {}'.format(filename), raw_text=True)

    def _disable_confirmation(self):
        self._send_config_commands(['terminal dont-ask'])

    def _load_config(self):
        cmd = 'rollback running file {0}'.format(self.replace_file.split('/')[-1])
        self._disable_confirmation()
        response = self._send_command(cmd, fmt='text')
        if 'Rollback failed' in response or response == []:
            return False
        return True

    def commit_config(self):
        if self.loaded:
            self.backup_file = 'config_' + str(datetime.now()).replace(' ', '_')
            self._save_config(self.backup_file)
            if self.replace:
                if self._load_config() is False:
                    raise ReplaceConfigException
            else:
                try:
                    self._commit_merge()
                    self.merge_candidate = ''  # clear the merge buffer
                except Exception as e:
                    raise MergeConfigException(str(e))

            self.changed = True
            self.loaded = False
        else:
            raise ReplaceConfigException('No config loaded.')

    def _delete_file(self, filename):
        commands = [
            'terminal dont-ask',
            'delete {}'.format(filename),
            'no terminal dont-ask'
        ]
        for command in commands:
            self._send_command(command, fmt='text')

    def discard_config(self):
        if self.loaded:
            self.merge_candidate = ''  # clear the buffer
        if self.loaded and self.replace:
            try:
                self._delete_file(self.fc.dst)
            except CLIError:
                pass
        self.loaded = False

    def _rollback_ssh(self, backup_file):
        result = self.device.send_command('rollback running-config file %s' % backup_file)
        if 'completed' not in result.lower():
            raise ReplaceConfigException(result)
        self._save_ssh()

    def rollback(self):
        if self.changed:
            if self.ssh_connection:
                self._rollback_ssh(self.backup_file)
            else:
                self.device.rollback(self.backup_file)
                self.device.save()
            self.changed = False

    def _apply_key_map(self, key_map, table):
        new_dict = {}
        for key, value in table.items():
            new_key = key_map.get(key)
            if new_key:
                new_dict[new_key] = str(value)
        return new_dict

    def _convert_uptime_to_seconds(self, uptime_facts):
        seconds = int(uptime_facts['up_days']) * 24 * 60 * 60
        seconds += int(uptime_facts['up_hours']) * 60 * 60
        seconds += int(uptime_facts['up_mins']) * 60
        seconds += int(uptime_facts['up_secs'])
        return seconds

    def _get_facts_ssh(self):
        final_facts = {}
        show_ver_output = json.loads(self.device.send_command_timing('show version | json'))
        uptime_facts = self._apply_key_map(UPTIME_KEY_MAP, show_ver_output)
        final_facts['uptime'] = self._convert_uptime_to_seconds(uptime_facts)
        final_facts['os_version'] = show_ver_output.get('kickstart_ver_str')
        final_facts['serial_number'] = show_ver_output.get('proc_board_id')
        final_facts['model'] = show_ver_output.get('chassis_id')
        final_facts['serial_number'] = show_ver_output.get('proc_board_id')
        final_facts['hostname'] = show_ver_output.get('host_name')

        final_facts['fqdn'] = json.loads(self.device.send_command(
                                'show hostname | json')).get('hostname')
        interfaces_output = self.device.send_command_timing('show interface status | json')
        interface_list = json.loads(interfaces_output)['TABLE_interface']['ROW_interface']
        interfaces = [intf['interface'] for intf in interface_list]
        final_facts['interface_list'] = interfaces
        final_facts['vendor'] = 'Cisco'
        return final_facts

    def _get_facts_api(self):
        pynxos_facts = self.device.facts
        final_facts = {key: value for key, value in pynxos_facts.items() if
                       key not in ['interfaces', 'uptime_string', 'vlans']}

        if pynxos_facts['interfaces']:
            final_facts['interface_list'] = pynxos_facts['interfaces']
        else:
            final_facts['interface_list'] = self.get_interfaces().keys()

        hostname_cmd = 'show hostname'
        hostname = self.device.show(hostname_cmd).get('hostname')

        final_facts['vendor'] = 'Cisco'
        if hostname:
            final_facts['fqdn'] = hostname
        return final_facts

    def get_facts(self):
        if self.ssh_connection:
            return self._get_facts_ssh()
        else:
            return self._get_facts_api()

    def get_interfaces(self):
        interfaces = {}
        cmd = 'show interface'
        interfaces_body = self._get_command_table(cmd, 'TABLE_interface', 'ROW_interface')

        for interface_details in interfaces_body:
            interface_name = interface_details.get('interface')
            # Earlier version of Nexus returned a list for 'eth_bw' (observed on 7.1(0)N1(1a))
            interface_speed = interface_details.get('eth_bw', 0)
            if isinstance(interface_speed, list):
                interface_speed = interface_speed[0]
            interface_speed = int(interface_speed) / 1000
            if 'admin_state' in interface_details:
                is_up = interface_details.get('admin_state', '') == 'up'
            else:
                is_up = interface_details.get('state', '') == 'up'
            interfaces[interface_name] = {
                'is_up': is_up,
                'is_enabled': (interface_details.get('state') == 'up'),
                'description': py23_compat.text_type(interface_details.get('desc', '').strip('"')),
                'last_flapped': self._compute_timestamp(
                    interface_details.get('eth_link_flapped', '')),
                'speed': int(interface_speed),
                'mac_address': napalm_base.helpers.convert(
                    napalm_base.helpers.mac, interface_details.get('eth_hw_addr')),
            }
        return interfaces

    def get_lldp_neighbors(self):
        results = {}
        lldp_raw_output = self._send_command('show lldp neighbors', fmt='text')
        lldp_neighbors = napalm_base.helpers.textfsm_extractor(
                            self, 'lldp_neighbors', lldp_raw_output)

        for neighbor in lldp_neighbors:
            local_iface = neighbor.get('local_interface')
            if neighbor.get(local_iface) is None:
                if local_iface not in results:
                    results[local_iface] = []

            neighbor_dict = {}
            neighbor_dict['hostname'] = py23_compat.text_type(neighbor.get('neighbor'))
            neighbor_dict['port'] = py23_compat.text_type(neighbor.get('neighbor_interface'))

            results[local_iface].append(neighbor_dict)
        return results

    def get_bgp_neighbors(self):
        results = {}
        cmd = 'show bgp sessions vrf all'
        vrf_list = self._get_command_table(cmd, 'TABLE_vrf', 'ROW_vrf')

        for vrf_dict in vrf_list:
            result_vrf_dict = {}
            result_vrf_dict['router_id'] = py23_compat.text_type(vrf_dict['router-id'])
            result_vrf_dict['peers'] = {}
            neighbors_list = vrf_dict.get('TABLE_neighbor', {}).get('ROW_neighbor', [])

            if isinstance(neighbors_list, dict):
                neighbors_list = [neighbors_list]

            for neighbor_dict in neighbors_list:
                neighborid = napalm_base.helpers.ip(neighbor_dict['neighbor-id'])

                result_peer_dict = {
                    'local_as': int(vrf_dict['local-as']),
                    'remote_as': int(neighbor_dict['remoteas']),
                    'remote_id': neighborid,
                    'is_enabled': True,
                    'uptime': -1,
                    'description': py23_compat.text_type(''),
                    'is_up': True
                }
                result_peer_dict['address_family'] = {
                    'ipv4': {
                        'sent_prefixes': -1,
                        'accepted_prefixes': -1,
                        'received_prefixes': -1
                    }
                }
                result_vrf_dict['peers'][neighborid] = result_peer_dict

            vrf_name = vrf_dict['vrf-name-out']
            if vrf_name == 'default':
                vrf_name = 'global'
            results[vrf_name] = result_vrf_dict
        return results

    def _send_config_commands(self, commands):
        if self.ssh_connection:
            for command in commands:
                self.device.send_command(command)
        else:
            self.device.config_list(commands)

    def _set_checkpoint(self, filename):
        commands = ['terminal dont-ask', 'checkpoint file {0}'.format(filename)]
        self._send_config_commands(commands)

    def _get_checkpoint_file(self):
        filename = 'temp_cp_file_from_napalm'
        self._set_checkpoint(filename)
        cp_out = self._send_command('show file {0}'.format(filename), fmt='text')
        self._delete_file(filename)
        return cp_out

    def get_lldp_neighbors_detail(self, interface=''):
        lldp_neighbors = {}
        filter = ''
        if interface:
            filter = 'interface {name} '.format(name=interface)

        command = 'show lldp neighbors {filter}detail'.format(filter=filter)
        # seems that some old devices may not return JSON output...

        lldp_neighbors_table_str = self._send_command(command, fmt='text')
        # thus we need to take the raw text output
        lldp_neighbors_list = lldp_neighbors_table_str.splitlines()

        if not lldp_neighbors_list:
            return lldp_neighbors  # empty dict

        CHASSIS_REGEX = '^(Chassis id:)\s+([a-z0-9\.]+)$'
        PORT_REGEX = '^(Port id:)\s+([0-9]+)$'
        LOCAL_PORT_ID_REGEX = '^(Local Port id:)\s+(.*)$'
        PORT_DESCR_REGEX = '^(Port Description:)\s+(.*)$'
        SYSTEM_NAME_REGEX = '^(System Name:)\s+(.*)$'
        SYSTEM_DESCR_REGEX = '^(System Description:)\s+(.*)$'
        SYST_CAPAB_REEGX = '^(System Capabilities:)\s+(.*)$'
        ENABL_CAPAB_REGEX = '^(Enabled Capabilities:)\s+(.*)$'
        VLAN_ID_REGEX = '^(Vlan ID:)\s+(.*)$'

        lldp_neighbor = {}
        interface_name = None

        for line in lldp_neighbors_list:
            chassis_rgx = re.search(CHASSIS_REGEX, line, re.I)
            if chassis_rgx:
                lldp_neighbor = {
                    'remote_chassis_id': napalm_base.helpers.mac(chassis_rgx.groups()[1])
                }
                continue
            lldp_neighbor['parent_interface'] = ''
            port_rgx = re.search(PORT_REGEX, line, re.I)
            if port_rgx:
                lldp_neighbor['parent_interface'] = py23_compat.text_type(port_rgx.groups()[1])
                continue
            local_port_rgx = re.search(LOCAL_PORT_ID_REGEX, line, re.I)
            if local_port_rgx:
                interface_name = local_port_rgx.groups()[1]
                continue
            port_descr_rgx = re.search(PORT_DESCR_REGEX, line, re.I)
            if port_descr_rgx:
                lldp_neighbor['remote_port'] = py23_compat.text_type(port_descr_rgx.groups()[1])
                lldp_neighbor['remote_port_description'] = py23_compat.text_type(
                                                            port_descr_rgx.groups()[1])
                continue
            syst_name_rgx = re.search(SYSTEM_NAME_REGEX, line, re.I)
            if syst_name_rgx:
                lldp_neighbor['remote_system_name'] = py23_compat.text_type(
                                                        syst_name_rgx.groups()[1])
                continue
            syst_descr_rgx = re.search(SYSTEM_DESCR_REGEX, line, re.I)
            if syst_descr_rgx:
                lldp_neighbor['remote_system_description'] = py23_compat.text_type(
                                                                syst_descr_rgx.groups()[1])
                continue
            syst_capab_rgx = re.search(SYST_CAPAB_REEGX, line, re.I)
            if syst_capab_rgx:
                lldp_neighbor['remote_system_capab'] = py23_compat.text_type(
                                                        syst_capab_rgx.groups()[1])
                continue
            syst_enabled_rgx = re.search(ENABL_CAPAB_REGEX, line, re.I)
            if syst_enabled_rgx:
                lldp_neighbor['remote_system_enable_capab'] = py23_compat.text_type(
                                                                syst_enabled_rgx.groups()[1])
                continue
            vlan_rgx = re.search(VLAN_ID_REGEX, line, re.I)
            if vlan_rgx:
                # at the end of the loop
                if interface_name not in lldp_neighbors.keys():
                    lldp_neighbors[interface_name] = []
                lldp_neighbors[interface_name].append(lldp_neighbor)
        return lldp_neighbors

    def cli(self, commands):
        cli_output = {}
        if type(commands) is not list:
            raise TypeError('Please enter a valid list of commands!')

        for command in commands:
            command_output = self._send_command(command, fmt='text')
            cli_output[py23_compat.text_type(command)] = command_output
        return cli_output

    def _send_command(self, command, fmt='json'):
        if self.ssh_connection:
            if fmt == 'json':
                command += ' | json'
                output = json.loads(self.device.send_command(command))
            else:
                output = self.device.send_command(command)
        else:
            try:
                if fmt == 'json':
                    output = self.device.show(command)
                else:
                    output = self.device.show(command, raw_text=True)
            except CLIError:
                output = []
            except ConnectionError:
                output = []
        return output

    def get_arp_table(self):
        arp_table = []
        command = 'show ip arp'

        arp_table_vrf = self._get_command_table(command, 'TABLE_vrf', 'ROW_vrf')
        arp_table_raw = self._get_table_rows(arp_table_vrf[0], 'TABLE_adj', 'ROW_adj')

        for arp_table_entry in arp_table_raw:
            raw_ip = arp_table_entry.get('ip-addr-out')
            raw_mac = arp_table_entry.get('mac')
            age = arp_table_entry.get('time-stamp')
            if age == '-':
                age_sec = float(-1)
            else:
                age_time = ''.join(age.split(':'))
                age_sec = float(
                    3600 * int(age_time[:2]) + 60 * int(age_time[2:4]) + int(age_time[4:])
                )
            interface = py23_compat.text_type(arp_table_entry.get('intf-out'))
            arp_table.append({
                'interface': interface,
                'mac': napalm_base.helpers.convert(
                    napalm_base.helpers.mac, raw_mac, raw_mac),
                'ip': napalm_base.helpers.ip(raw_ip),
                'age': age_sec
            })
        return arp_table

    def _get_ntp_entity(self, peer_type):
        ntp_entities = {}
        command = 'show ntp peers'
        ntp_peers_table = self._get_command_table(command, 'TABLE_peers', 'ROW_peers')

        for ntp_peer in ntp_peers_table:
            if ntp_peer.get('serv_peer', '').strip() != peer_type:
                continue
            peer_addr = napalm_base.helpers.ip(ntp_peer.get('PeerIPAddress').strip())
            ntp_entities[peer_addr] = {}

        return ntp_entities

    def get_ntp_peers(self):
        return self._get_ntp_entity('Peer')

    def get_ntp_servers(self):
        return self._get_ntp_entity('Server')

    def get_ntp_stats(self):
        ntp_stats = []
        command = 'show ntp peer-status'
        ntp_stats_table = self._get_command_table(command, 'TABLE_peersstatus', 'ROW_peersstatus')

        for ntp_peer in ntp_stats_table:
            peer_address = napalm_base.helpers.ip(ntp_peer.get('remote').strip())
            syncmode = ntp_peer.get('syncmode')
            stratum = int(ntp_peer.get('st'))
            hostpoll = int(ntp_peer.get('poll'))
            reachability = int(ntp_peer.get('reach'))
            delay = float(ntp_peer.get('delay'))
            ntp_stats.append({
                'remote': peer_address,
                'synchronized': (syncmode == '*'),
                'referenceid': peer_address,
                'stratum': stratum,
                'type': '',
                'when': '',
                'hostpoll': hostpoll,
                'reachability': reachability,
                'delay': delay,
                'offset': 0.0,
                'jitter': 0.0
            })
        return ntp_stats

    def get_interfaces_ip(self):
        interfaces_ip = {}
        ipv4_command = 'show ip interface'
        ipv4_interf_table_vrf = self._get_command_table(ipv4_command, 'TABLE_intf', 'ROW_intf')

        for interface in ipv4_interf_table_vrf:
            interface_name = py23_compat.text_type(interface.get('intf-name', ''))
            address = napalm_base.helpers.ip(interface.get('prefix'))
            prefix = int(interface.get('masklen', ''))
            if interface_name not in interfaces_ip.keys():
                interfaces_ip[interface_name] = {}
            if 'ipv4' not in interfaces_ip[interface_name].keys():
                interfaces_ip[interface_name]['ipv4'] = {}
            if address not in interfaces_ip[interface_name].get('ipv4'):
                interfaces_ip[interface_name]['ipv4'][address] = {}
            interfaces_ip[interface_name]['ipv4'][address].update({
                'prefix_length': prefix
            })
            secondary_addresses = interface.get('TABLE_secondary_address', {})\
                                           .get('ROW_secondary_address', [])
            if type(secondary_addresses) is dict:
                secondary_addresses = [secondary_addresses]
            for secondary_address in secondary_addresses:
                secondary_address_ip = napalm_base.helpers.ip(secondary_address.get('prefix1'))
                secondary_address_prefix = int(secondary_address.get('masklen1', ''))
                if 'ipv4' not in interfaces_ip[interface_name].keys():
                    interfaces_ip[interface_name]['ipv4'] = {}
                if secondary_address_ip not in interfaces_ip[interface_name].get('ipv4'):
                    interfaces_ip[interface_name]['ipv4'][secondary_address_ip] = {}
                interfaces_ip[interface_name]['ipv4'][secondary_address_ip].update({
                    'prefix_length': secondary_address_prefix
                })

        ipv6_command = 'show ipv6 interface'
        ipv6_interf_table_vrf = self._get_command_table(ipv6_command, 'TABLE_intf', 'ROW_intf')

        for interface in ipv6_interf_table_vrf:
            interface_name = py23_compat.text_type(interface.get('intf-name', ''))
            address = napalm_base.helpers.ip(interface.get('addr', '').split('/')[0])
            prefix = interface.get('prefix', '').split('/')[-1]
            if prefix:
                prefix = int(interface.get('prefix', '').split('/')[-1])
            else:
                prefix = 128
            if interface_name not in interfaces_ip.keys():
                interfaces_ip[interface_name] = {}
            if 'ipv6' not in interfaces_ip[interface_name].keys():
                interfaces_ip[interface_name]['ipv6'] = {}
            if address not in interfaces_ip[interface_name].get('ipv6'):
                interfaces_ip[interface_name]['ipv6'][address] = {}
            interfaces_ip[interface_name]['ipv6'][address].update({
                'prefix_length': prefix
            })
            secondary_addresses = interface.get('TABLE_sec_addr', {}).get('ROW_sec_addr', [])
            if type(secondary_addresses) is dict:
                secondary_addresses = [secondary_addresses]
            for secondary_address in secondary_addresses:
                sec_prefix = secondary_address.get('sec-prefix', '').split('/')
                secondary_address_ip = napalm_base.helpers.ip(sec_prefix[0])
                secondary_address_prefix = int(sec_prefix[-1])
                if 'ipv6' not in interfaces_ip[interface_name].keys():
                    interfaces_ip[interface_name]['ipv6'] = {}
                if secondary_address_ip not in interfaces_ip[interface_name].get('ipv6'):
                    interfaces_ip[interface_name]['ipv6'][secondary_address_ip] = {}
                interfaces_ip[interface_name]['ipv6'][secondary_address_ip].update({
                    'prefix_length': secondary_address_prefix
                })
        return interfaces_ip

    def get_mac_address_table(self):
        mac_table = []
        command = 'show mac address-table'
        mac_table_raw = self._get_command_table(command, 'TABLE_mac_address', 'ROW_mac_address')

        for mac_entry in mac_table_raw:
            raw_mac = mac_entry.get('disp_mac_addr')
            interface = py23_compat.text_type(mac_entry.get('disp_port'))
            vlan = int(mac_entry.get('disp_vlan'))
            active = True
            static = (mac_entry.get('disp_is_static') != '0')
            moves = 0
            last_move = 0.0
            mac_table.append({
                'mac': napalm_base.helpers.mac(raw_mac),
                'interface': interface,
                'vlan': vlan,
                'active': active,
                'static': static,
                'moves': moves,
                'last_move': last_move
            })
        return mac_table

    def get_snmp_information(self):
        snmp_information = {}
        snmp_command = 'show running-config'
        snmp_raw_output = self._send_command(snmp_command, fmt='text')
        snmp_config = napalm_base.helpers.textfsm_extractor(self, 'snmp_config', snmp_raw_output)

        if not snmp_config:
            return snmp_information

        snmp_information = {
            'contact': py23_compat.text_type(''),
            'location': py23_compat.text_type(''),
            'community': {},
            'chassis_id': py23_compat.text_type('')
        }

        for snmp_entry in snmp_config:
            contact = py23_compat.text_type(snmp_entry.get('contact', ''))
            if contact:
                snmp_information['contact'] = contact
            location = py23_compat.text_type(snmp_entry.get('location', ''))
            if location:
                snmp_information['location'] = location

            community_name = py23_compat.text_type(snmp_entry.get('community', ''))
            if not community_name:
                continue

            if community_name not in snmp_information['community'].keys():
                snmp_information['community'][community_name] = {
                    'acl': py23_compat.text_type(snmp_entry.get('acl', '')),
                    'mode': py23_compat.text_type(snmp_entry.get('mode', '').lower())
                }
            else:
                acl = py23_compat.text_type(snmp_entry.get('acl', ''))
                if acl:
                    snmp_information['community'][community_name]['acl'] = acl
                mode = py23_compat.text_type(snmp_entry.get('mode', '').lower())
                if mode:
                    snmp_information['community'][community_name]['mode'] = mode
        return snmp_information

    def get_users(self):
        _CISCO_TO_CISCO_MAP = {
            'network-admin': 15,
            'network-operator': 5
        }

        _DEFAULT_USER_DICT = {
            'password': '',
            'level': 0,
            'sshkeys': []
        }

        users = {}
        command = 'show running-config'
        section_username_raw_output = self._send_command(command, fmt='text')
        section_username_tabled_output = napalm_base.helpers.textfsm_extractor(
            self, 'users', section_username_raw_output)

        for user in section_username_tabled_output:
            username = user.get('username', '')
            if not username:
                continue
            if username not in users:
                users[username] = _DEFAULT_USER_DICT.copy()

            password = user.get('password', '')
            if password:
                users[username]['password'] = py23_compat.text_type(password.strip())

            level = 0
            role = user.get('role', '')
            if role.startswith('priv'):
                level = int(role.split('-')[-1])
            else:
                level = _CISCO_TO_CISCO_MAP.get(role, 0)
            if level > users.get(username).get('level'):
                # unfortunately on Cisco you can set different priv levels for the same user
                # Good news though: the device will consider the highest level
                users[username]['level'] = level

            sshkeytype = user.get('sshkeytype', '')
            sshkeyvalue = user.get('sshkeyvalue', '')
            if sshkeytype and sshkeyvalue:
                if sshkeytype not in ['ssh-rsa', 'ssh-dsa']:
                    continue
                users[username]['sshkeys'].append(py23_compat.text_type(sshkeyvalue))
        return users

    def traceroute(self,
                   destination,
                   source=c.TRACEROUTE_SOURCE,
                   ttl=c.TRACEROUTE_TTL,
                   timeout=c.TRACEROUTE_TIMEOUT,
                   vrf=c.TRACEROUTE_VRF):
        _HOP_ENTRY_PROBE = [
            '\s+',
            '(',  # beginning of host_name (ip_address) RTT group
            '(',  # beginning of host_name (ip_address) group only
            '([a-zA-Z0-9\.:-]*)',  # hostname
            '\s+',
            '\(?([a-fA-F0-9\.:][^\)]*)\)?'  # IP Address between brackets
            ')?',  # end of host_name (ip_address) group only
            # also hostname/ip are optional -- they can or cannot be specified
            # if not specified, means the current probe followed the same path as the previous
            '\s+',
            '(\d+\.\d+)\s+ms',  # RTT
            '|\*',  # OR *, when non responsive hop
            ')'  # end of host_name (ip_address) RTT group
        ]

        _HOP_ENTRY = [
            '\s?',  # space before hop index?
            '(\d+)',  # hop index
        ]

        traceroute_result = {}
        timeout = 5  # seconds
        probes = 3  # 3 probes/jop and this cannot be changed on NXOS!

        version = ''
        try:
            version = '6' if IPAddress(destination).version == 6 else ''
        except AddrFormatError:
            return {'error': 'Destination doest not look like a valid IP Address: {}'.format(
                destination)}

        source_opt = ''
        if source:
            source_opt = 'source {source}'.format(source=source)

        command = 'traceroute{version} {destination} {source_opt}'.format(
            version=version,
            destination=destination,
            source_opt=source_opt
        )

        try:
            traceroute_raw_output = self._send_command(command, fmt='text')
        except CommandErrorException:
            return {'error': 'Cannot execute traceroute on the device: {}'.format(command)}

        hop_regex = ''.join(_HOP_ENTRY + _HOP_ENTRY_PROBE * probes)
        traceroute_result['success'] = {}
        if traceroute_raw_output:
            for line in traceroute_raw_output.splitlines():
                hop_search = re.search(hop_regex, line)
                if not hop_search:
                    continue
                hop_details = hop_search.groups()
                hop_index = int(hop_details[0])
                previous_probe_host_name = '*'
                previous_probe_ip_address = '*'
                traceroute_result['success'][hop_index] = {'probes': {}}
                for probe_index in range(probes):
                    host_name = hop_details[3+probe_index*5]
                    ip_address_raw = hop_details[4+probe_index*5]
                    ip_address = napalm_base.helpers.convert(
                        napalm_base.helpers.ip, ip_address_raw, ip_address_raw)
                    rtt = hop_details[5+probe_index*5]
                    if rtt:
                        rtt = float(rtt)
                    else:
                        rtt = timeout * 1000.0
                    if not host_name:
                        host_name = previous_probe_host_name
                    if not ip_address:
                        ip_address = previous_probe_ip_address
                    if hop_details[1+probe_index*5] == '*':
                        host_name = '*'
                        ip_address = '*'
                    traceroute_result['success'][hop_index]['probes'][probe_index+1] = {
                        'host_name': py23_compat.text_type(host_name),
                        'ip_address': py23_compat.text_type(ip_address),
                        'rtt': rtt
                    }
                    previous_probe_host_name = host_name
                    previous_probe_ip_address = ip_address
        return traceroute_result

    def get_config(self, retrieve='all'):
        config = {
            'startup': '',
            'running': '',
            'candidate': ''
        }  # default values

        if retrieve.lower() in ('running', 'all'):
            _cmd = 'show running-config'
            config['running'] = py23_compat.text_type(self._send_command(_cmd, fmt='text'))
        if retrieve.lower() in ('startup', 'all'):
            _cmd = 'show startup-config'
            config['startup'] = py23_compat.text_type(self._send_command(_cmd, fmt='text'))
        return config
