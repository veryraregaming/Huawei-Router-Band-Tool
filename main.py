import sys

# Global exception hook to suppress Windows-specific errors
def global_exception_handler(exctype, value, traceback):
    # Suppress Windows-specific errors that we can't fix
    error_msg = str(value)
    if (exctype == TypeError and ("WPARAM is simple" in error_msg or 
                                "WNDPROC return value cannot be converted to LRESULT" in error_msg)):
        # Silently ignore these specific Windows-related errors
        return
    # For all other exceptions, use the default exception handler
    sys.__excepthook__(exctype, value, traceback)

# Set the global exception hook
sys.excepthook = global_exception_handler

import tkinter as tk
from tkinter import messagebox, ttk, Checkbutton, IntVar, filedialog, scrolledtext
import json
import requests
import xml.etree.ElementTree as ET
import time
import threading
import socket
import subprocess
import platform
import base64
import hashlib
import os
from datetime import datetime
import inspect
import webbrowser
import ipaddress
import random
import uuid
from math import log10
from statistics import mean, median
import speedtest
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from win10toast import ToastNotifier
import pystray
from PIL import Image
from io import BytesIO
import re

# Import tooltips
try:
    from tooltips import create_tooltip
    TOOLTIPS_AVAILABLE = True
except ImportError:
    TOOLTIPS_AVAILABLE = False
    def create_tooltip(widget, text):
        # Dummy function if tooltips not available
        pass

# Import speedtest-cli for speed testing
try:
    import speedtest
    SPEEDTEST_AVAILABLE = True
except ImportError:
    SPEEDTEST_AVAILABLE = False

# Huawei LTE API integration - modern API access method
try:
    from huawei_lte_api.Client import Client
    from huawei_lte_api.AuthorizedConnection import AuthorizedConnection
    from huawei_lte_api.Connection import Connection
    HUAWEI_API_AVAILABLE = True
except ImportError:
    HUAWEI_API_AVAILABLE = False

# Define supported bands lists for fallback when scanning fails
SUPPORTED_4G_BANDS = ["B1", "B3", "B7", "B8", "B20", "B28", "B32", "B38", "B40", "B41", "B42"]
SUPPORTED_5G_BANDS = ["n1", "n3", "n28", "n41", "n78", "n79"]

# Theoretical maximum speeds by band and network type
THEORETICAL_SPEEDS = {
    # Network type: {band: (max_download_mbps, max_upload_mbps)}
    "4G": {
        "B1": (150, 50),
        "B3": (300, 75),
        "B7": (300, 75),
        "B8": (100, 35),
        "B20": (150, 50),
        "B28": (150, 50),
        "B32": (100, 50),
        "B38": (200, 50),
        "B40": (200, 50),
        "B41": (200, 50),
        "B42": (200, 50),
    },
    "4G+": {
        "B1": (300, 75),
        "B3": (450, 100),
        "B7": (450, 100),
        "B8": (150, 50),
        "B20": (300, 75),
        "B28": (300, 75),
        "B32": (150, 75),
        "B38": (300, 75),
        "B40": (300, 75),
        "B41": (300, 75),
        "B42": (300, 75),
    },
    "5G": {
        # These are very approximate for 5G NSA (depends heavily on implementation)
        "B1": (900, 150),
        "B3": (1000, 200),
        "B7": (1000, 200),
        "B28": (800, 150),
        "B41": (2000, 300),
        "B42": (2000, 300),
    }
}

# Signal quality adjustment factors
SIGNAL_QUALITY_FACTORS = {
    # RSRP ranges: Factor to multiply theoretical max by
    (-80, 0): 1.0,     # Excellent (-80 to 0 dBm)
    (-90, -80): 0.9,   # Good (-90 to -80 dBm)
    (-100, -90): 0.7,  # Fair (-100 to -90 dBm)
    (-110, -100): 0.5, # Poor (-110 to -100 dBm)
    (-120, -110): 0.3, # Very poor (-120 to -110 dBm)
    (-999, -120): 0.1  # Extremely poor (less than -120 dBm)
}

# Function to estimate theoretical maximum speed
def estimate_max_speed(band, network_type, rsrp, sinr):
    """
    Estimate theoretical maximum speed based on band, network type and signal quality
    
    Args:
        band: The band (e.g., "B1", "B3")
        network_type: Network type (e.g., "4G", "4G+", "5G")
        rsrp: RSRP value in dBm
        sinr: SINR value in dB
    
    Returns:
        Tuple of (max_download_mbps, max_upload_mbps)
    """
    # Default values if we don't have specific data
    default_speeds = {
        "2G": (0.3, 0.1),
        "3G": (7, 2),
        "4G": (150, 50),
        "4G+": (300, 75),
        "5G": (1000, 200)
    }
    
    # Normalize network type
    normalized_type = network_type
    if network_type == "LTE":
        normalized_type = "4G"
    elif "LTE-CA" in network_type or "4G+" in network_type:
        normalized_type = "4G+"
    elif "5G" in network_type:
        normalized_type = "5G"
    
    # Get the first band if multiple bands are used
    first_band = band.split(",")[0].strip() if "," in band else band.strip()
    if first_band.startswith("B"):
        band_key = first_band
    else:
        band_key = f"B{first_band}"
    
    # Get base theoretical speed
    if normalized_type in THEORETICAL_SPEEDS and band_key in THEORETICAL_SPEEDS[normalized_type]:
        max_dl, max_ul = THEORETICAL_SPEEDS[normalized_type][band_key]
    else:
        # If network type or band not in our database, use default
        max_dl, max_ul = default_speeds.get(normalized_type, default_speeds["4G"])
    
    # Apply signal quality adjustment
    try:
        rsrp_float = float(rsrp.replace("dBm", "")) if isinstance(rsrp, str) and "dBm" in rsrp else float(rsrp)
        signal_factor = 0.5  # Default medium factor
        
        # Find the appropriate signal quality factor based on RSRP
        for (min_val, max_val), factor in SIGNAL_QUALITY_FACTORS.items():
            if min_val <= rsrp_float < max_val:
                signal_factor = factor
                break
                
        # SINR also impacts speed - higher SINR means better modulation
        sinr_float = float(sinr.replace("dB", "")) if isinstance(sinr, str) and "dB" in sinr else float(sinr)
        sinr_factor = 0.5
        
        if sinr_float > 20:
            sinr_factor = 1.0
        elif sinr_float > 13:
            sinr_factor = 0.9
        elif sinr_float > 10:
            sinr_factor = 0.8
        elif sinr_float > 5:
            sinr_factor = 0.6
        else:
            sinr_factor = 0.4
            
        # Combined factor (weighted average)
        combined_factor = (signal_factor * 0.7) + (sinr_factor * 0.3)
        
        # Apply to max speeds
        adjusted_dl = max_dl * combined_factor
        adjusted_ul = max_ul * combined_factor
        
        return adjusted_dl, adjusted_ul
        
    except (ValueError, TypeError):
        # If we can't parse RSRP as a number, return unadjusted speeds
        return max_dl, max_ul

# Load or create configuration file
def load_config():
    try:
        with open("config.json", "r") as file:
            return json.load(file)
    except FileNotFoundError:
        return {
            "router_ip": "", 
            "username": "", 
            "password": "", 
            "selected_bands": [], 
            "auto_connect": False, 
            "use_api_lib": True,
            "speedtest_on_startup": False
        }

def save_config(config):
    with open("config.json", "w") as file:
        json.dump(config, file, indent=4)

# Network diagnostic tools
def ping_host(host):
    param = '-n' if platform.system().lower() == 'windows' else '-c'
    command = ['ping', param, '1', host]
    try:
        output = subprocess.check_output(command, stderr=subprocess.STDOUT, universal_newlines=True, timeout=5)
        if "TTL=" in output or "ttl=" in output:
            return True, output
        else:
            return False, output
    except subprocess.CalledProcessError as e:
        return False, str(e.output)
    except Exception as e:
        return False, str(e)

def check_network_connectivity():
    try:
        socket.create_connection(("8.8.8.8", 53), timeout=3)
        return True
    except OSError:
        return False

def get_default_gateway():
    if platform.system().lower() != 'windows':
        return None
    try:
        output = subprocess.check_output('ipconfig', universal_newlines=True)
        for line in output.split('\n'):
            if "Default Gateway" in line:
                gateway = line.split(':')[1].strip()
                if gateway:
                    return gateway
    except Exception:
        pass
    return None

# Common Huawei Router IPs
COMMON_ROUTER_IPS = ["192.168.1.1", "192.168.8.1", "192.168.100.1", "192.168.3.1"]

# Band number to hex mapping
BAND_MAP = {
    1: 0x1, 3: 0x4, 7: 0x40, 8: 0x80, 20: 0x80000, 28: 0x8000000, 32: 0x80000000,
    38: 0x40000000000, 40: 0x100000000000, 41: 0x200000000000, 42: 0x400000000000
}

# API Endpoints
STATUS_ENDPOINT = "/api/monitoring/status"
LOGIN_ENDPOINT = "/api/user/login"
BAND_LOCK_ENDPOINT = "/api/net/net-mode"
TOKEN_ENDPOINT = "/api/webserver/SesTokInfo"
INFO_ENDPOINT = "/api/device/information"
PLMN_ENDPOINT = "/api/net/current-plmn"
NET_MODE_ENDPOINT = "/api/net/net-mode"
CELL_INFO_ENDPOINT = "/api/net/cell-info"
SESSION_ENDPOINT = "/api/user/state-login"
SET_MONITORING_ENDPOINT = "/api/monitoring/set-monitoring"

# Expanded list of signal and status endpoints
SIGNAL_ENDPOINTS = [
    "/api/device/signal",
    "/api/net/signal",
    "/api/monitoring/status",
    "/api/device/information",
    "/api/monitoring/traffic-statistics",
    "/api/monitoring/check-notifications",
    "/api/monitoring/converged-status",
    "/api/monitoring/statistic",
    "/api/net/current-cell-info",
    "/api/monitoring/station-status",
    "/api/monitoring/status-wlan",
    "/api/wlan/station-information",
    "/api/dialup/connection"
]

# Password Encryption (matching C# HuaweiPasswordEncrypt)
def encrypt_password(username, password, csrf_token):
    encoded_username = base64.b64encode(username.encode()).decode()
    encoded_password = base64.b64encode(password.encode()).decode()
    encoded_csrf_token = base64.b64encode(csrf_token.encode()).decode()
    to_hash = f"{encoded_username}#{encoded_password}#{encoded_csrf_token}"
    sha256_hash = hashlib.sha256(to_hash.encode()).digest()
    final_password = base64.b64encode(sha256_hash).decode()
    return final_password

# Login to Router - API First approach with fallback to legacy method
def login_to_router(ip, username, password, use_api_lib=True):
    # Try Huawei LTE API library first if available and enabled
    if HUAWEI_API_AVAILABLE and use_api_lib:
        try:
            # Build the URL for the API connection
            url = f"http://{username}:{password}@{ip}/"
            
            # Create authorized connection and client
            connection = AuthorizedConnection(url)
            client = Client(connection)
            
            # Test the connection with a simple API call
            device_info = client.device.information()
            
            # Return client object instead of session for API-based approach
            return client, None, f"Login Successful (API) - {device_info.get('devicename', '')} {device_info.get('HardwareVersion', '')}"
        except Exception as e:
            error_msg = f"API login failed: {str(e)}. Falling back to legacy method."
            print(error_msg)
            # Fall back to legacy login method
            
    # Legacy login method (original implementation)
    session = requests.Session()
    login_url = f"http://{ip}{LOGIN_ENDPOINT}"
    token_url = f"http://{ip}{TOKEN_ENDPOINT}"
    session_url = f"http://{ip}{SESSION_ENDPOINT}"
    
    reachable, ping_result = ping_host(ip)
    if not reachable:
        return None, None, f"Router at {ip} is not reachable. Check your connection and IP address."
    
    try:
        # Fetch session token
        response = session.get(token_url, timeout=10)
        if response.status_code != 200:
            return None, None, f"Failed to get CSRF token (Status: {response.status_code})"
        token_data = ET.fromstring(response.text)
        session_id = token_data.find("SesInfo").text
        token = token_data.find("TokInfo").text
        
        # Make a preliminary request to /api/user/state-login
        headers = {
            "__RequestVerificationToken": token,
            "Cookie": f"SessionID={session_id}",
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
            "Referer": f"http://{ip}/html/home.html"
        }
        response = session.get(session_url, headers=headers, timeout=10)
        if response.status_code == 200:
            print(f"Session state response: {response.text}")
        else:
            print(f"Session state request failed (Status: {response.status_code})")
        
        # Encrypt the password
        encrypted_password = encrypt_password(username, password, token)
        login_payload = f"""
        <request>
            <Username>{username}</Username>
            <Password>{encrypted_password}</Password>
            <password_type>4</password_type>
        </request>
        """
        headers = {
            "Content-Type": "application/xml",
            "__RequestVerificationToken": token,
            "Cookie": f"SessionID={session_id}",
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
            "Referer": f"http://{ip}/html/home.html"
        }
        
        # Try different payloads for /api/monitoring/set-monitoring
        monitoring_payloads = [
            """
            <request>
                <EnableSignalMonitoring>1</EnableSignalMonitoring>
                <EnableDetailedMetrics>1</EnableDetailedMetrics>
            </request>
            """,
            """
            <request>
                <Enable>1</Enable>
            </request>
            """,
            """
            <request>
                <SignalMonitoring>1</SignalMonitoring>
            </request>
            """
        ]
        
        for i, payload in enumerate(monitoring_payloads):
            print(f"Attempting monitoring payload {i+1}: {payload.strip()}")
            response = session.post(f"http://{ip}{SET_MONITORING_ENDPOINT}", data=payload, headers=headers, timeout=10)
            if response.status_code == 200:
                print(f"Monitoring payload {i+1} (Status: {response.status_code}, Response: {response.text})")
            else:
                print(f"Monitoring payload {i+1} failed (Status: {response.status_code}, Response: {response.text})")
        
        response = session.post(login_url, data=login_payload, headers=headers, timeout=10)
        if response.status_code == 200:
            info_response = session.get(f"http://{ip}{INFO_ENDPOINT}", headers=headers, timeout=10)
            if info_response.status_code == 200:
                info_data = ET.fromstring(info_response.text)
                firmware = info_data.find("firmwareversion")
                if firmware is not None:
                    return session, token, f"Login Successful (Firmware: {firmware.text})"
            return session, token, "Login Successful"
        else:
            return None, None, f"Login Failed (Status: {response.status_code})"
    except requests.exceptions.ConnectTimeout:
        return None, None, f"Connection to {ip} timed out. Verify the router is powered on and the IP is correct."
    except requests.exceptions.ConnectionError:
        return None, None, f"Cannot connect to {ip}. Check if the router is online and accessible."
    except ET.ParseError:
        return None, None, f"Received invalid XML from router. The device at {ip} may not be a Huawei router."
    except Exception as e:
        error_type = type(e).__name__
        return None, None, f"Connection Error ({error_type}): {str(e)}"

# Fetch Signal Data using huawei-lte-api library
def fetch_signal_data_api(self, client, ip):
    try:
        # Initialize dictionary to store signal data
        signal_data = {}
        
        # Get device signal data
        device_signal = client.device.signal()
        
        # Extract relevant signal quality data
        if isinstance(device_signal, dict):
            signal_data['rsrp'] = f"{device_signal.get('rsrp', '--')} dBm"
            signal_data['rsrq'] = f"{device_signal.get('rsrq', '--')} dB"
            signal_data['sinr'] = f"{device_signal.get('sinr', '--')} dB"
            signal_data['band'] = device_signal.get('band', '--')
            
            # Convert band information to user-friendly format if needed
            if signal_data['band'] and isinstance(signal_data['band'], str) and signal_data['band'].startswith("LTE BAND"):
                signal_data['band'] = f"B{signal_data['band'].replace('LTE BAND', '').strip()}"
            
            # Get connection status for network information
            try:
                status_info = client.monitoring.status()
                if isinstance(status_info, dict):
                    signal_data['mode'] = status_info.get('CurrentNetworkTypeEx', 'LTE')
                    
                    # Make the network type more user friendly
                    if signal_data['mode'] == '101':
                        signal_data['mode'] = '5G NSA'
                    elif signal_data['mode'] == '38':
                        signal_data['mode'] = 'NR/5G'
                    elif signal_data['mode'] == '7':
                        signal_data['mode'] = 'LTE'
                    
                    signal_data['plmn'] = status_info.get('CurrentNetworkOperatorName', '--')
            except Exception as e:
                self.log_message(f"Error getting connection status via API: {str(e)}", log_type="detailed")
        
        # Get recent speedtest results from our stored data if available
        recent_speedtest = self.get_recent_speedtest_results()
        if recent_speedtest:
            signal_data['download'] = f"{recent_speedtest.get('download', '0.00')} Mbps"
            signal_data['upload'] = f"{recent_speedtest.get('upload', '0.00')} Mbps"
        
        return signal_data
        
    except Exception as e:
        self.log_message(f"Error fetching signal data from API: {str(e)}", log_type="detailed")
        return {}

# Unified fetch_signal_data function
def fetch_signal_data(self, session, ip, token):
    # Check if we're using huawei-lte-api client
    if hasattr(self, 'client') and self.client is not None and self.use_api_lib.get():
        return fetch_signal_data_api(self, self.client, ip)
    
    try:
        # Initialize dictionary to store signal data
        signal_data = {}
        
        # Get signal information using API calls
        headers = {
            'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
            'Cookie': f'SessionID={token}'
        }
        
        # Make API request for signal info
        response = session.post(f'http://{ip}/api/device/signal', headers=headers)
        if response.status_code == 200:
            try:
                data = response.json()
                if 'response' in data:
                    signal_data['rsrp'] = f"{data['response'].get('rsrp', '--')} dBm"
                    signal_data['rsrq'] = f"{data['response'].get('rsrq', '--')} dB"
                    signal_data['sinr'] = f"{data['response'].get('sinr', '--')} dB"
                    signal_data['band'] = data['response'].get('band', '--')
                    
                    # Make band info more user-friendly
                    if signal_data['band'] and isinstance(signal_data['band'], str) and signal_data['band'].startswith("LTE BAND"):
                        signal_data['band'] = f"B{signal_data['band'].replace('LTE BAND', '').strip()}"
            except ValueError:
                self.log_message("Error parsing signal data response", log_type="detailed")
        
        # Get connection status for network type and provider
        status_response = session.post(f'http://{ip}/api/monitoring/status', headers=headers)
        if status_response.status_code == 200:
            try:
                status_data = status_response.json()
                if 'response' in status_data:
                    signal_data['mode'] = status_data['response'].get('CurrentNetworkTypeEx', 'LTE')
                    
                    # Make the network type more user-friendly
                    if signal_data['mode'] == '101':
                        signal_data['mode'] = '5G NSA'
                    elif signal_data['mode'] == '38':
                        signal_data['mode'] = 'NR/5G'
                    elif signal_data['mode'] == '7':
                        signal_data['mode'] = 'LTE'
                        
                    signal_data['plmn'] = status_data['response'].get('CurrentNetworkOperatorName', '--')
            except ValueError:
                self.log_message("Error parsing status data response", log_type="detailed")
        
        # Get recent speedtest results from our stored data if available
        recent_speedtest = self.get_recent_speedtest_results()
        if recent_speedtest:
            signal_data['download'] = f"{recent_speedtest.get('download', '0.00')} Mbps"
            signal_data['upload'] = f"{recent_speedtest.get('upload', '0.00')} Mbps"
        
        return signal_data
        
    except Exception as e:
        self.log_message(f"Error fetching signal data: {str(e)}", log_type="detailed")
        return {}

# Get connection status
def get_connection_status(session, ip, token):
    # Check if we're using huawei-lte-api client
    if HUAWEI_API_AVAILABLE and isinstance(session, Client):
        try:
            # Get status information using the API
            status_info = session.monitoring.status()
            
            # Extract connection and network type
            connection_status = status_info.get('ConnectionStatus', 'Unknown')
            network_type = status_info.get('CurrentNetworkType', 'Unknown')
            
            # Map network type to text
            network_types = {
                "0": "No Service", "1": "GSM", "2": "GPRS", "3": "EDGE", "4": "WCDMA",
                "5": "HSDPA", "6": "HSUPA", "7": "HSPA", "8": "TD-SCDMA", "9": "HSPA+",
                "19": "LTE", "20": "LTE-CA (4G+)", "21": "5G NSA", "22": "5G SA"
            }
            
            return {
                "status": connection_status,
                "network_type": network_types.get(network_type, f"Unknown ({network_type})")
            }
        except Exception as e:
            return {"status": "Error", "network_type": f"API Error ({str(e)})"}
    
    # Legacy implementation for regular requests.Session
    try:
        url = f"http://{ip}{STATUS_ENDPOINT}"
        headers = {
            "__RequestVerificationToken": token,
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
            "Referer": f"http://{ip}/html/home.html"
        }
        response = session.get(url, headers=headers, timeout=10)
        if response.status_code == 200:
            data = ET.fromstring(response.text)
            status = data.find("ConnectionStatus")
            network_type = data.find("CurrentNetworkType")
            network_types = {
                "0": "No Service", "1": "GSM", "2": "GPRS", "3": "EDGE", "4": "WCDMA",
                "5": "HSDPA", "6": "HSUPA", "7": "HSPA", "8": "TD-SCDMA", "9": "HSPA+",
                "19": "LTE", "20": "LTE-CA (4G+)", "21": "5G NSA", "22": "5G SA"
            }
            return {
                "status": status.text if status is not None else "Unknown",
                "network_type": network_types.get(network_type.text, f"Unknown ({network_type.text})") if network_type is not None else "Unknown"
            }
        return {"status": "Unknown", "network_type": "Unknown"}
    except Exception as e:
        return {"status": "Error", "network_type": f"Error ({str(e)})"}

# Apply Band Lock
def apply_band_lock(session, ip, token, selected_bands):
    """Apply band lock configuration"""
    if not selected_bands:
        raise ValueError("No bands selected for locking")
        
    # Check if we're using huawei-lte-api client
    if isinstance(session, Client):
        try:
            # Convert selected bands to LTE band hex format
            band_numbers = []
            for band in selected_bands:
                if isinstance(band, str):
                    if band.startswith("B"):
                        band_numbers.append(int(band[1:]))
                    elif band.isdigit():
                        band_numbers.append(int(band))
                elif isinstance(band, int):
                    band_numbers.append(band)
            
            band_hex = sum(BAND_MAP.get(num, 0) for num in band_numbers) or 0x3FFFFFFF  # Default to all bands if none selected
            band_hex_str = format(band_hex, 'X')
            
            # Get current settings
            current_mode = session.net.net_mode()
            
            # Set the new mode using the correct parameter names
            response = session.net.set_net_mode(
                lteband=band_hex_str,
                networkband=current_mode.get('NetworkBand', '3FFFFFFF'),
                networkmode=current_mode.get('NetworkMode', '03')
            )
            
            if response == 'OK':
                return True
            elif isinstance(response, dict):
                if 'result' in response and response['result'] == 'success':
                    return True
                elif 'error' in response:
                    error_code = response.get('error', {}).get('code', 'Unknown')
                    error_msg = response.get('error', {}).get('message', 'Unknown')
                    if error_code == '112003':  # Unsupported band error
                        raise Exception(f"Band not supported by device")
                    raise Exception(f"API band lock error: {error_code}: {error_msg}")
            return False
        except Exception as e:
            if '112003' in str(e):  # Unsupported band error
                raise Exception(f"Band not supported by this device")
            raise Exception(f"Failed to apply band lock: {str(e)}")
    else:
        # Web interface fallback implementation
        try:
            # Convert band list to hex format
            band_numbers = [int(band[1:]) for band in selected_bands if isinstance(band, str) and band.startswith("B")]
            band_hex = sum(BAND_MAP.get(num, 0) for num in band_numbers) or 0x3FFFFFFF
            band_hex_str = format(band_hex, 'X')
            
            # Get CSRF token
            response = session.get(f"http://{ip}{TOKEN_ENDPOINT}", timeout=10)
            if response.status_code != 200:
                raise Exception("Failed to get CSRF token")
            token = ET.fromstring(response.text).find("TokInfo").text
            
            # Prepare and send band lock request
            payload = f"""
            <request>
                <NetworkMode>03</NetworkMode>
                <LTEBand>{band_hex_str}</LTEBand>
            </request>
            """
            headers = {
                "Content-Type": "application/xml",
                "__RequestVerificationToken": token,
                "User-Agent": "Mozilla/5.0",
                "Referer": f"http://{ip}/html/home.html"
            }
            
            response = session.post(f"http://{ip}{BAND_LOCK_ENDPOINT}", data=payload, headers=headers, timeout=15)
            if response.status_code != 200:
                raise Exception(f"Band lock failed with status code: {response.status_code}")
            return True
        except Exception as e:
            raise Exception(f"Web interface band lock failed: {str(e)}")

# Speed test function
def run_speedtest(server_id=None):
    """Run a speedtest and return the results"""
    try:
        # Configure speedtest
        s = speedtest.Speedtest()
        s.get_best_server()
        
        # Run tests
        s.download()
        s.upload()
        
        # Get results
        results = s.results.dict()
        return {
            'success': True,
            'download': results['download'] / 1_000_000,  # Convert to Mbps
            'upload': results['upload'] / 1_000_000,
            'ping': results['ping'],
            'server': results.get('server', {}).get('name', 'Unknown')
        }
    except Exception as e:
        if "Malformed speedtest.net configuration" in str(e):
            # Retry once with a different server if configuration error
            try:
                s = speedtest.Speedtest()
                servers = s.get_servers()
                if servers:
                    # Try the second best server
                    server_list = list(servers.values())[0]
                    if len(server_list) > 1:
                        s.get_best_server(server_list[1:])
                    s.download()
                    s.upload()
                    results = s.results.dict()
                    return {
                        'success': True,
                        'download': results['download'] / 1_000_000,
                        'upload': results['upload'] / 1_000_000,
                        'ping': results['ping'],
                        'server': results.get('server', {}).get('name', 'Unknown')
                    }
            except Exception as retry_error:
                return {
                    'success': False,
                    'message': f"Speed test failed after retry: {str(retry_error)}"
                }
        return {
            'success': False,
            'message': f"Speed test failed: {str(e)}"
        }

# Create reports directory if not exists
def ensure_reports_dir():
    reports_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reports")
    if not os.path.exists(reports_dir):
        os.makedirs(reports_dir)
    return reports_dir

# Generate a report file with date and time
def generate_report(results, optimisation_type="basic"):
    """Generate a report file with date and time"""
    ensure_reports_dir()
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    report_path = os.path.join("reports", f"optimisation_report_{timestamp}.txt")
    
    with open(report_path, "w") as f:
        f.write(f"Band Optimisation Report\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Optimisation Type: {optimisation_type}\n\n")
        
        # Sort results by score (higher is better)
        sorted_results = sorted(results.items(), key=lambda x: x[1]['score'], reverse=True)
        
        f.write("Individual Band Results:\n")
        f.write("------------------------\n")
        
        for band, result in sorted_results:
            rsrp = result.get('rsrp', 'Unknown')
            sinr = result.get('sinr', 'Unknown')
            # Include network type (4G/5G)
            network_type = result.get('network_type', '4G')  # Default to 4G if not specified
            
            f.write(f"Band: B{band}\n")
            f.write(f"  Network Type: {network_type}\n")
            f.write(f"  RSRP: {rsrp}\n")
            f.write(f"  SINR: {sinr}\n")
            
            # Include theoretical speeds if available
            if 'theoretical_dl_mbps' in result:
                f.write(f"  Theoretical Download: {result['theoretical_dl_mbps']:.2f} Mbps\n")
            
            if 'theoretical_ul_mbps' in result:
                f.write(f"  Theoretical Upload: {result['theoretical_ul_mbps']:.2f} Mbps\n")
            
            # Include actual speeds if available
            if 'download_mbps' in result and 'upload_mbps' in result:
                f.write(f"  Measured Download: {result['download_mbps']:.2f} Mbps\n")
                f.write(f"  Measured Upload: {result['upload_mbps']:.2f} Mbps\n")
                
            if 'ping_ms' in result:
                f.write(f"  Ping: {result['ping_ms']:.3f} ms\n")
                
                if 'dl_efficiency' in result:
                    f.write(f"  Download Efficiency: {result['dl_efficiency']:.1f}%\n")
                
                if 'ul_efficiency' in result:
                    f.write(f"  Upload Efficiency: {result['ul_efficiency']:.1f}%\n")
                
                if 'signal_score' in result and 'speed_score' in result:
                    f.write(f"  Signal Score: {result['signal_score']}\n")
                    f.write(f"  Speed Score: {result['speed_score']}\n")
            else:
                # If speedtest failed, explain why this band might still be valuable
                f.write(f"  Note: Speedtest failed\n")
            
            f.write(f"  Score: {result['score']}\n")
            f.write("\n")
        
        f.write("Recommendations:\n")
        f.write("----------------\n")
        
        # Get the top 3 bands
        best_bands = sorted_results[:min(3, len(sorted_results))]
        
        if best_bands:
            best_band = best_bands[0]
            best_band_str = f"B{best_band[0]}"
            f.write(f"Best band: {best_band_str} (Score: {best_band[1]['score']})\n")
            
            recommended_bands = ", ".join([f"B{b[0]}" for b in best_bands])
            f.write(f"Recommended combination: {recommended_bands}\n\n")
            
            # Add explanation of why bands are recommended even if speedtest failed
            f.write("Selection Logic:\n")
            f.write("---------------\n")
            f.write("Bands are ranked based on a combination of signal quality (RSRP and SINR) metrics.\n")
            f.write("Even if speedtests fail, bands with good signal quality may provide better overall performance.\n")
            f.write("The optimal configuration typically combines bands with complementary characteristics:\n")
            f.write("- Lower bands (B8, B20, B28) provide better coverage and building penetration\n")
            f.write("- Higher bands (B1, B3, B7) provide better speeds in good conditions\n\n")
            
            # List which bands have efficiency data
            has_efficiency = []
            for band, result in sorted_results:
                if 'dl_efficiency' in result or 'ul_efficiency' in result:
                    has_efficiency.append((band, result))
            
            if has_efficiency:
                f.write("Efficiency Summary:\n")
                f.write("------------------\n")
                
                for band, result in has_efficiency:
                    band_str = f"B{band}"
                    dl_eff = result.get('dl_efficiency', 'N/A')
                    ul_eff = result.get('ul_efficiency', 'N/A')
                    
                    if dl_eff != 'N/A':
                        dl_eff = f"{dl_eff:.1f}%"
                    
                    if ul_eff != 'N/A':
                        ul_eff = f"{ul_eff:.1f}%"
                    
                    f.write(f"{band_str}: Download efficiency: {dl_eff}, Upload efficiency: {ul_eff}\n")
        else:
            f.write("No recommended bands found.\n")
    
    return os.path.abspath(report_path)

class BandOptimiserApp(tk.Frame):
    def __init__(self, master=None):
        super().__init__(master)
        self.master = master
        self.pack(fill=tk.BOTH, expand=True)
        
        # Initialize config
        self.config = {}
        
        # Initialize variables
        self.router_ip = tk.StringVar(value="192.168.8.1")
        self.username = tk.StringVar(value="admin")
        self.password = tk.StringVar(value="")
        self.token = None
        self.session = None
        self.client = None
        self.is_connected = False
        self.api_restriction_warning_shown = False
        self.signal_update_interval = 30000  # 30 seconds
        self.poll_status_task = None  # Initialize to track auto-refresh
        
        # UI state variables
        self.status_var = tk.StringVar(value="Not Connected")
        self.auto_connect = tk.BooleanVar(value=False)
        self.use_api_lib = tk.BooleanVar(value=True)
        self.auto_refresh = tk.BooleanVar(value=False)
        self.monitor_bands = tk.BooleanVar(value=False)
        self.run_speed_on_start = tk.BooleanVar(value=False)
        self.minimize_to_tray = tk.BooleanVar(value=False)
        
        # Band selection variables
        self.band_vars = {}
        for band in SUPPORTED_4G_BANDS:
            band_name = f"B{band}"
            self.band_vars[band_name] = tk.BooleanVar()
        
        for band in SUPPORTED_5G_BANDS:
            band_name = f"n{band}"
            self.band_vars[band_name] = tk.BooleanVar()
        
        # Network aggregation variables
        self.upload_band_vars = {}
        self.download_band_vars = {}
        
        # Initialize available bands with defaults
        self.available_bands = {
            "4G": SUPPORTED_4G_BANDS,
            "5G": SUPPORTED_5G_BANDS
        }
        
        # Initialize band variables for network aggregation
        for band_num in [1, 3, 7, 8]:
            band = f"B{band_num}"
            self.upload_band_vars[band] = tk.BooleanVar()
            self.download_band_vars[band] = tk.BooleanVar()
        
        # Create dictionary for signal information display
        self.signal_info = {
            "RSRP": tk.StringVar(value="--"),
            "RSRQ": tk.StringVar(value="--"),
            "SINR": tk.StringVar(value="--"),
            "BAND": tk.StringVar(value="--"),
            "NETWORK_TYPE": tk.StringVar(value="--"),
            "CARRIER": tk.StringVar(value="--"),
            "DOWNLOAD": tk.StringVar(value="--"),
            "UPLOAD": tk.StringVar(value="--")
        }
        
        # Create log text widget for detailed status display
        self.log_text = None
        
        # Set icon path
        self.icon_path = "assets/icon.ico"
        
        # Initialize tray icon to None
        self.tray_icon = None
        
        # Create UI elements
        self.create_menu()
        self.create_main_frame()
        
        # Set window title and size
        self.master.title("Huawei CPE Pro 2 Band Scanner and Optimizer")
        self.master.geometry("800x600")
        self.master.minsize(800, 600)
        
        # Set icon
        try:
            self.master.iconbitmap(self.icon_path)
        except:
            pass
        
        # Load config file if available
        self.load_config()
        
        # Auto-connect if enabled
        if self.auto_connect.get():
            self.connect()
            
        # Initialize system tray
        self.setup_tray_icon()
        
        # Log startup message
        self.log_message("Application started", log_type="both")

    def load_config(self):
        """Load saved configuration"""
        try:
            config = load_config()
            
            # Apply configuration to variables
            self.router_ip.set(config.get("router_ip", "192.168.8.1"))
            self.username.set(config.get("username", "admin"))
            self.password.set(config.get("password", ""))  # Load the password directly
            
            # Load other settings
            self.auto_connect.set(config.get("auto_connect", False))
            self.use_api_lib.set(config.get("use_api_lib", True))
            self.run_speed_on_start.set(config.get("speedtest_on_startup", False))
            self.auto_refresh.set(config.get("auto_refresh", False))
            self.monitor_bands.set(config.get("monitor_bands", False))
            self.minimize_to_tray.set(config.get("minimize_to_tray", False))
            
            # Load band selections
            selected_bands = config.get("selected_bands", [])
            for band_name, var in self.band_vars.items():
                var.set(band_name in selected_bands)
                
            self.log_message("Configuration loaded", log_type="detailed")
        except Exception as e:
            # If this is the first run, the log_message method might not exist yet
            # so just print to console instead
            print(f"Error loading configuration: {str(e)}")

    def create_menu(self):
        # Create top menu
        menubar = tk.Menu(self.master)
        self.master.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Connect", command=self.connect)
        file_menu.add_command(label="Disconnect", command=self.disconnect)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.exit_app)  # Use exit_app instead of master.quit
        
        # Tools menu
        tools_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="Run Speedtest", command=self.start_speedtest)
        
        # Options menu
        options_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Options", menu=options_menu)
        options_menu.add_checkbutton(label="Auto Refresh", variable=self.auto_refresh, 
                                    command=self.toggle_auto_refresh)
        options_menu.add_checkbutton(label="Monitor and Lock Bands", variable=self.monitor_bands,
                                    command=self.save_config)
        options_menu.add_checkbutton(label="Minimize to Tray on Close", variable=self.minimize_to_tray,
                                   command=self.save_config)  # Ensure this saves config when changed
        
        # Skip the Help menu entirely to avoid missing function references
        
        # Add auto-connect option
        options_menu.add_checkbutton(
            label="Auto-Connect at Startup", 
            variable=self.auto_connect, 
            command=self.save_config
        )
        
        # Add API library option
        options_menu.add_checkbutton(
            label="Use Huawei LTE API Library", 
            variable=self.use_api_lib, 
            command=self.save_config
        )
        
        # Add speedtest on startup option
        options_menu.add_checkbutton(
            label="Run Speedtest on Startup", 
            variable=self.run_speed_on_start, 
            command=self.save_config
        )
        
        # Add optimise button
        options_menu.add_command(
            label="Optimise Bands", 
            command=self.optimise
        )
        
        # Add enhanced optimise button
        options_menu.add_command(
            label="Enhanced Optimise", 
            command=self.enhanced_optimise
        )
        
        # Add donate menu
        options_menu.add_command(
            label="Donate", 
            command=self.show_donation_dialog
        )

    def create_main_frame(self):
        # Create a frame for the main content
        main_frame = ttk.Frame(self.master, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Connection panel
        conn_frame = ttk.LabelFrame(main_frame, text="Router Connection", padding="10")
        conn_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(conn_frame, text="Router IP:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(conn_frame, textvariable=self.router_ip).grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        
        ttk.Label(conn_frame, text="Username:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(conn_frame, textvariable=self.username).grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
        
        ttk.Label(conn_frame, text="Password:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
        password_entry = ttk.Entry(conn_frame, textvariable=self.password, show="*")
        password_entry.grid(row=2, column=1, sticky=tk.W, padx=5, pady=5)
        
        # Options frame
        options_frame = ttk.Frame(conn_frame)
        options_frame.grid(row=0, column=2, rowspan=3, padx=10)
        
        auto_connect_cb = ttk.Checkbutton(options_frame, text="Auto-connect at startup", variable=self.auto_connect)
        auto_connect_cb.pack(anchor=tk.W, pady=2)
        
        if HUAWEI_API_AVAILABLE:
            api_lib_cb = ttk.Checkbutton(options_frame, text="Use Huawei LTE API library", variable=self.use_api_lib)
            api_lib_cb.pack(anchor=tk.W, pady=2)
        
        speedtest_startup_cb = ttk.Checkbutton(options_frame, text="Run Speedtest on Startup", variable=self.run_speed_on_start)
        speedtest_startup_cb.pack(anchor=tk.W, pady=2)
        
        minimize_tray_cb = ttk.Checkbutton(options_frame, text="Minimize to Tray on Close", variable=self.minimize_to_tray)
        minimize_tray_cb.pack(anchor=tk.W, pady=2)
        
        # Connect button
        self.connect_button = ttk.Button(conn_frame, text="Connect", command=self.connect)
        self.connect_button.grid(row=0, column=3, rowspan=3, padx=10)
        
        # Create tooltip for connect button
        if TOOLTIPS_AVAILABLE:
            create_tooltip(self.connect_button, "Connect to your Huawei router using the provided IP address and credentials")
        
        # Create two-column layout with proper weighting
        content_frame = ttk.Frame(main_frame)
        content_frame.pack(fill=tk.BOTH, expand=True, pady=2)
        content_frame.columnconfigure(0, weight=1)  # Left column
        content_frame.columnconfigure(1, weight=1)  # Right column
        
        # Left column for controls and signal info
        left_col = ttk.Frame(content_frame)
        left_col.grid(row=0, column=0, sticky="nsew", padx=(0, 2))
        
        # Signal information section - more compact
        signal_frame = ttk.LabelFrame(left_col, text="Signal Information", padding="5")
        signal_frame.pack(fill=tk.X, pady=2)
        
        self.signal_info = {}
        signal_labels = [
            ("RSRP (dBm):", "RSRP", "--"),
            ("RSRQ (dB):", "RSRQ", "--"),
            ("SINR (dB):", "SINR", "--"),
            ("Current Band:", "BAND", "--"),
            ("Network Type:", "NETWORK_TYPE", "LTE"),
            ("Provider:", "CARRIER", "--"),
            ("Download:", "DOWNLOAD", "0.00 Mbps"),
            ("Upload:", "UPLOAD", "0.00 Mbps")
        ]
        
        # Create 2-column layout for signal info (4 items per row)
        for i, (label_text, key, default) in enumerate(signal_labels):
            row, col = divmod(i, 2)
            ttk.Label(signal_frame, text=label_text).grid(row=row, column=col*2, sticky=tk.W, padx=2, pady=1)
            self.signal_info[key] = tk.StringVar(value=default)
            ttk.Label(signal_frame, textvariable=self.signal_info[key]).grid(row=row, column=col*2+1, sticky=tk.W, padx=2, pady=1)
        
        # Refresh signal button row
        refresh_frame = ttk.Frame(signal_frame)
        refresh_frame.grid(row=len(signal_labels)//2, column=0, columnspan=4, pady=2)
        
        self.refresh_button = ttk.Button(refresh_frame, text="Refresh Signal", command=self.refresh_signal)
        self.refresh_button.pack(side=tk.LEFT, padx=2)
        create_tooltip(self.refresh_button, "Refresh signal information to show current band, signal strength, and network type (4G/5G)")
        
        auto_refresh_cb = ttk.Checkbutton(refresh_frame, text="Auto-refresh", 
                                         variable=self.auto_refresh, 
                                         command=self.toggle_auto_refresh)
        auto_refresh_cb.pack(side=tk.LEFT, padx=5)
        
        # Improved band selection and network management section
        bands_frame = ttk.LabelFrame(left_col, text="Band Selection & Management", padding="5")
        bands_frame.pack(fill=tk.BOTH, expand=True, pady=2)
        
        # Create notebook with tabs for 4G and 5G bands
        band_notebook = ttk.Notebook(bands_frame)
        band_notebook.pack(fill=tk.BOTH, expand=True)
        
        # 4G Band tab
        self.band_section_4g = ttk.Frame(band_notebook)
        band_notebook.add(self.band_section_4g, text="4G Bands")
        
        # 5G Band tab
        self.band_section_5g = ttk.Frame(band_notebook)
        band_notebook.add(self.band_section_5g, text="5G Bands")
        
        # Create common button frame that applies to both tabs
        band_buttons_frame = ttk.Frame(bands_frame)
        band_buttons_frame.pack(fill=tk.X, pady=2)
        
        select_all_button = ttk.Button(band_buttons_frame, text="Select All Bands", 
                                      command=lambda: self.toggle_all_bands(True),
                                      width=15)
        select_all_button.pack(side=tk.LEFT, padx=2)
        create_tooltip(select_all_button, "Select all available frequency bands (both 4G and 5G) for testing")
        
        clear_all_button = ttk.Button(band_buttons_frame, text="Clear All Bands", 
                                     command=lambda: self.toggle_all_bands(False),
                                     width=15)
        clear_all_button.pack(side=tk.LEFT, padx=2)
        create_tooltip(clear_all_button, "Clear all band selections (both 4G and 5G)")
        
        self.apply_bands_button = ttk.Button(band_buttons_frame, text="Apply Selection", 
                                 command=self.apply_band_selection,
                                 width=15)
        self.apply_bands_button.pack(side=tk.LEFT, padx=2)
        create_tooltip(self.apply_bands_button, "Apply the selected bands to your router - allows only the selected bands to be used")
        
        # Advanced Options section
        ttk.Separator(bands_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=5)
        
        # Add explanation text
        explanation = ttk.Label(bands_frame, text="Advanced Options:", font=("", 9, "bold"))
        explanation.pack(anchor=tk.W, padx=5, pady=2)
        
        explanation_text = ttk.Label(bands_frame, text="Network aggregation allows separate control of upload/download bands.\n"
                                    "Network mode allows quick switching between 2G/3G/4G/5G modes.",
                                   wraplength=350, justify=tk.LEFT)
        explanation_text.pack(fill=tk.X, padx=5, pady=2)
        
        # Network Aggregation section
        aggregation_frame = ttk.LabelFrame(bands_frame, text="Network Aggregation", padding="5")
        aggregation_frame.pack(fill=tk.X, pady=2)
        
        # Create headers and more compact layout
        agg_grid = ttk.Frame(aggregation_frame)
        agg_grid.pack(fill=tk.X)
        
        ttk.Label(agg_grid, text="Upload band").grid(row=0, column=0, padx=5, pady=1)
        ttk.Label(agg_grid, text="Download band").grid(row=0, column=1, padx=5, pady=1)
        
        # Add band checkboxes in 2-column layout
        for i, band_num in enumerate([1, 3, 7, 8]):
            band = f"B{band_num}"
            row = i + 1
            upload_cb = ttk.Checkbutton(agg_grid, text=band, 
                                        variable=self.upload_band_vars[band])
            upload_cb.grid(row=row, column=0, sticky=tk.W, padx=5, pady=1)
            
            download_cb = ttk.Checkbutton(agg_grid, text=band, 
                                          variable=self.download_band_vars[band])
            download_cb.grid(row=row, column=1, sticky=tk.W, padx=5, pady=1)
        
        # Network Mode Quickswitch section
        quickswitch_frame = ttk.LabelFrame(bands_frame, text="Network Mode Quickswitch", padding="5")
        quickswitch_frame.pack(fill=tk.X, pady=2)
        
        # Network mode dropdown and apply in same row
        mode_frame = ttk.Frame(quickswitch_frame)
        mode_frame.pack(fill=tk.X, pady=2)
        
        self.network_mode = tk.StringVar(value="4G + 5G")
        network_modes = ["2G only", "3G only", "4G only", "4G + 5G", "5G only", "2G + 3G + 4G", "All modes"]
        
        mode_dropdown = ttk.Combobox(mode_frame, textvariable=self.network_mode, 
                                     values=network_modes, state="readonly", width=15)
        mode_dropdown.pack(side=tk.LEFT, padx=2, pady=2, fill=tk.X, expand=True)
        
        apply_mode_button = ttk.Button(mode_frame, text="Apply", 
                                       command=self.apply_network_mode, width=10)
        apply_mode_button.pack(side=tk.LEFT, padx=2, pady=2)
        create_tooltip(apply_mode_button, "Apply the selected network mode (2G/3G/4G/5G) to your router")
        
        # Apply network configuration button for aggregation
        apply_network_button = ttk.Button(bands_frame, text="Apply Network Configuration", 
                                         command=self.apply_network_config)
        apply_network_button.pack(pady=5)
        create_tooltip(apply_network_button, "Apply the network aggregation settings - allows separate control of upload and download bands")
        
        # Right column - Log and Actions
        right_col = ttk.Frame(content_frame)
        right_col.grid(row=0, column=1, sticky="nsew", padx=(2, 0))
        
        # Action buttons section - more compact grid layout
        action_frame = ttk.LabelFrame(right_col, text="Actions", padding="5")
        action_frame.pack(fill=tk.X, pady=2)
        
        # Create 2x2 grid for action buttons
        action_grid = ttk.Frame(action_frame)
        action_grid.pack(fill=tk.X, padx=5, pady=2)
        
        self.optimise_button = ttk.Button(action_grid, text="Optimise Bands", 
                                        command=self.optimise, width=18)
        self.optimise_button.grid(row=0, column=0, padx=2, pady=2, sticky="ew")
        create_tooltip(self.optimise_button, "Automatically test all frequency bands for both 4G and 5G connections. Evaluates signal quality metrics (RSRP, SINR) and recommends the best combination based on coverage and reliability.")
        
        self.enhanced_optimise_button = ttk.Button(action_grid, text="Enhanced Optimise", 
                                                command=self.enhanced_optimise, width=18)
        self.enhanced_optimise_button.grid(row=0, column=1, padx=2, pady=2, sticky="ew")
        create_tooltip(self.enhanced_optimise_button, "Advanced optimisation that tests all bands with both signal quality AND speed tests. Tests both 4G and 5G, runs actual speed tests for each band, and provides the most accurate recommendations.")
        
        self.speedtest_button = ttk.Button(action_grid, text="Speed Test", 
                                         command=self.start_speedtest, width=18)
        self.speedtest_button.grid(row=1, column=0, padx=2, pady=2, sticky="ew")
        create_tooltip(self.speedtest_button, "Run a speed test using the current band configuration. Tests download and upload speeds using the nearest server.")
        
        # Log section
        log_frame = ttk.LabelFrame(right_col, text="Log", padding="5")
        log_frame.pack(fill=tk.BOTH, expand=True, pady=2)
        
        # Create tabbed log interface
        log_notebook = ttk.Notebook(log_frame)
        log_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Standard Log Tab (user-friendly)
        standard_log_frame = ttk.Frame(log_notebook)
        log_notebook.add(standard_log_frame, text="Standard")
        
        standard_log_container = ttk.Frame(standard_log_frame)
        standard_log_container.pack(fill=tk.BOTH, expand=True)
        
        self.log_text = tk.Text(standard_log_container, wrap=tk.WORD, height=15)
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        standard_log_scrollbar = ttk.Scrollbar(standard_log_container, command=self.log_text.yview)
        standard_log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.config(yscrollcommand=standard_log_scrollbar.set)
        
        # Detailed Log Tab (verbose technical information)
        detailed_log_frame = ttk.Frame(log_notebook)
        log_notebook.add(detailed_log_frame, text="Detailed")
        
        detailed_log_container = ttk.Frame(detailed_log_frame)
        detailed_log_container.pack(fill=tk.BOTH, expand=True)
        
        self.detailed_log_text = tk.Text(detailed_log_container, wrap=tk.WORD, height=15)
        self.detailed_log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        detailed_log_scrollbar = ttk.Scrollbar(detailed_log_container, command=self.detailed_log_text.yview)
        detailed_log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.detailed_log_text.config(yscrollcommand=detailed_log_scrollbar.set)
        
        # Status bar
        self.status_var = tk.StringVar(value="Disconnected")
        status_bar = ttk.Label(self.master, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Initial log message
        self.log_message("Application started")
        self.log_message("Connect to your Huawei router to begin")
        
        # Initialize band UI
        self.update_band_selection_ui()

    def log_message(self, message, log_type="both", replace_last=False):
        """Log a message to the console and/or detailed log
        
        Args:
            message: The message to log
            log_type: Where to log the message ("standard", "detailed", or "both")
            replace_last: Whether to replace the last log entry (useful for progress updates)
        """
        # Add timestamp to message
        timestamp = datetime.now().strftime("%H:%M:%S")
        timestamped_message = f"[{timestamp}] {message}"
        
        try:
            # Log to standard log if requested
            if log_type in ["standard", "both"]:
                if hasattr(self, 'log_text') and self.log_text is not None:
                    if replace_last:
                        # Delete the last line
                        self.log_text.delete("end-1l", "end")
                    self.log_text.insert(tk.END, timestamped_message + "\n")
                    self.log_text.see(tk.END)  # Scroll to the end
            
            # Log to detailed log if requested
            if log_type in ["detailed", "both"]:
                if hasattr(self, 'detailed_log_text') and self.detailed_log_text is not None:
                    if replace_last:
                        # Delete the last line
                        self.detailed_log_text.delete("end-1l", "end")
                    self.detailed_log_text.insert(tk.END, timestamped_message + "\n")
                    self.detailed_log_text.see(tk.END)  # Scroll to the end
            
            # Also print to console for debugging
            print(timestamped_message)
        except TypeError as e:
            # Suppress the WPARAM TypeError which can occur with Windows tray icon integration
            if "WPARAM is simple" in str(e):
                # Silently ignore this specific Windows-related error
                pass
            else:
                # For other TypeError exceptions, still log to console
                print(f"[{timestamp}] {message}")
                print(f"[{timestamp}] Error logging: {str(e)}")
        except Exception as e:
            # If we can't log to the UI, at least print to console
            print(f"[{timestamp}] {message}")
            print(f"[{timestamp}] Error logging: {str(e)}")
    
    def connect(self):
        """Connect to the router"""
        # Don't connect if already connected
        if self.is_connected:
            self.log_message("Already connected", log_type="both")
            return
            
        # Get connection details
        ip = self.router_ip.get()
        username = self.username.get()
        password = self.password.get()
        use_api = self.use_api_lib.get()
        
        # Validate inputs
        if not ip or not username or not password:
            messagebox.showerror("Error", "Please enter router IP, username and password")
            return
            
        # Update UI
        self.status_var.set("Connecting...")
        self.log_message(f"Connecting to {ip}...", log_type="both")
        
        # Start connection thread
        self.connect_button.config(state=tk.DISABLED)
        threading.Thread(target=lambda: self.connect_thread(ip, username, password, use_api)).start()
    
    def connect_thread(self, ip, username, password, use_api):
        """Background thread for connecting to router"""
        try:
            # Connect to router
            result = login_to_router(ip, username, password, use_api)
            
            # Process connection result on main thread
            self.master.after(0, lambda: self.handle_connection_result(result, ip))
        except Exception as e:
            # Log error and update UI on main thread
            self.master.after(0, lambda: self.log_message(f"Connection error: {str(e)}", log_type="both"))
            self.master.after(0, lambda: self.status_var.set("Connection failed"))
            self.master.after(0, lambda: self.connect_button.config(state=tk.NORMAL))
    
    def handle_connection_result(self, result, ip):
        """Handle connection result"""
        if result[0]:
            # Store the session object
            if isinstance(result[0], Client):
                self.client = result[0]
                self.session = None
                self.log_message("Connected using Huawei LTE API", log_type="both")
            else:
                self.session = result[0]
                self.token = result[1]
                self.log_message("Connected using web interface", log_type="both")
            
            # Store credentials in config
            self.config["router_ip"] = ip
            self.config["username"] = self.username.get()
            self.config["password"] = self.password.get()
            self.config["auto_connect"] = self.auto_connect.get()
            self.config["use_api_lib"] = self.use_api_lib.get()
            self.config["speedtest_on_startup"] = self.run_speed_on_start.get()
            save_config(self.config)
            
            # Update UI
            self.is_connected = True
            self.status_var.set("Connected")
            self.connect_button.config(text="Disconnect", command=self.disconnect, state=tk.NORMAL)
            self.refresh_button.config(state=tk.NORMAL)
            
            # Set flag for initial connection notification
            self.send_initial_notification = True
            
            # Scan for available bands
            self.log_message("Scanning for available bands...", log_type="both")
            try:
                self.available_bands = scan_available_bands(self.client or self.session, ip, self.token)
                self.log_message(f"Available 4G bands: {', '.join(self.available_bands['4G'])}", log_type="both")
                self.log_message(f"Available 5G bands: {', '.join(self.available_bands['5G'])}", log_type="both")
                
                # Update band selection UI with available bands
                self.update_band_selection_ui()
            except Exception as e:
                self.log_message(f"Error scanning bands: {str(e)}", log_type="both")
            
            # Refresh signal data
            self.refresh_signal()
            
            # Run initial speedtest if enabled
            if self.run_speed_on_start.get():
                self._run_initial_speedtest()
        else:
            # Connection failed
            error_msg = result[1] if len(result) > 1 else "Unknown error"
            self.log_message(f"Connection failed: {error_msg}", log_type="both")
            self.status_var.set("Connection failed")
            self.connect_button.config(text="Connect", command=self.connect, state=tk.NORMAL)
    
    def _run_initial_speedtest(self):
        """Run initial speed test after connection"""
        self.log_message("🚀 Starting speedtest.net measurement (will take 15-30 seconds)...", log_type="standard")
        
        # Run in background thread
        def initial_speedtest_thread():
            try:
                # Show progress updates
                progress_steps = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
                progress_task = None
                
                def update_progress(step=0):
                    nonlocal progress_task
                    symbol = progress_steps[step % len(progress_steps)]
                    self.log_message(f"{symbol} Speedtest in progress... (this may take 15-30 seconds)", log_type="standard", replace_last=True)
                    progress_task = self.master.after(500, lambda: update_progress(step + 1))
                
                # Start progress updates
                update_progress()
                
                # Run a standard speedtest
                result = run_speedtest()
                
                # Cancel progress updates
                if progress_task:
                    self.master.after_cancel(progress_task)
                
                if result["success"]:
                    dl = result["download"]
                    ul = result["upload"]
                    ping = result["ping"]
                    server = result["server"]
                    
                    # Save speedtest results for use in update_signal_ui
                    self.last_speedtest_time = time.time()
                    self.last_speedtest_dl = dl
                    self.last_speedtest_ul = ul
                    
                    # Update signal information with the new speed values
                    self.signal_info["DOWNLOAD"].set(f"{dl:.2f} Mbps")
                    self.signal_info["UPLOAD"].set(f"{ul:.2f} Mbps")
                    
                    # Log the initial speed test results
                    self.log_message(f"✅ Speedtest.net results: {dl:.2f} Mbps down, {ul:.2f} Mbps up, {ping:.2f} ms ping", log_type="standard")
                    self.log_message(f"Server used: {server}", log_type="detailed")
                else:
                    self.log_message(f"⚠️ Speedtest failed: {result['message']}", log_type="both")
            except Exception as e:
                self.log_message(f"⚠️ Error during speedtest: {str(e)}", log_type="both")
        
        threading.Thread(target=initial_speedtest_thread, daemon=True).start()
    
    def disconnect(self):
        """Disconnect from the router"""
        if not self.is_connected:
            return
            
        # Reset state
        self.is_connected = False
        self.client = None
        self.session = None
        self.token = None
        
        # Update UI
        self.status_var.set("Disconnected")
        self.connect_button.config(text="Connect", command=self.connect)
        self.refresh_button.config(state=tk.DISABLED)
        
        # Stop auto-refresh if enabled
        if self.auto_refresh.get():
            self.toggle_auto_refresh()
        
        # Log message
        self.log_message("Disconnected from router", log_type="both")
    
    def refresh_signal(self):
        # Disable refresh button while refreshing
        if hasattr(self, 'refresh_button'):
            self.refresh_button.config(state=tk.DISABLED)
        
        # Run in background thread
        threading.Thread(target=self.refresh_thread, daemon=True).start()

    def refresh_thread(self):
        """Background thread for refreshing signal data"""
        try:
            # Get router IP
            ip = self.router_ip.get()
            token = self.token
            
            # Get the current band before refresh (if available)
            previous_band = None
            if hasattr(self, 'signal_info') and 'BAND' in self.signal_info:
                previous_band = self.signal_info['BAND'].get()
            
            # Fetch the signal data using the appropriate method
            if self.client is not None:
                # Using the API library
                signal_data = fetch_signal_data_api(self, self.client, ip)
            elif self.session is not None:
                # Using web requests
                signal_data = fetch_signal_data(self, self.session, ip, token)
            else:
                self.log_message("No active session or client available", log_type="both")
                return
            
            # Update UI with the signal data
            if signal_data:
                # Log the data for debugging
                self.log_message(f"Signal data received: {signal_data}", log_type="detailed")
                
                # Check if the band has changed since the previous check
                current_band = signal_data.get('band', 'N/A')
                band_changed = (
                    previous_band is not None and 
                    current_band is not None and 
                    current_band != 'N/A' and 
                    current_band != '--' and 
                    current_band != previous_band
                )
                
                # Determine if we need to show a notification
                show_notification = False
                
                # Show notification when first connected
                if hasattr(self, 'send_initial_notification') and self.send_initial_notification:
                    show_notification = True
                    self.send_initial_notification = False  # Reset the flag
                
                # Show notification if the band has changed
                elif band_changed:
                    show_notification = True
                    self.log_message(f"Band changed: {previous_band} → {current_band}", log_type="both")
                
                # Show notification if needed
                if show_notification and current_band and current_band != 'N/A' and current_band != '--':
                    try:
                        toaster = ToastNotifier()
                        
                        # Get network technology information
                        mode = signal_data.get('mode', '')
                        network_type = "Unknown"
                        
                        # Determine network technology type
                        if "LTE" in mode:
                            if "LTE+" in mode or "LTE-A" in mode:
                                network_type = "4G+"
                            else:
                                network_type = "4G"
                        elif "NR" in mode or "5G" in mode:
                            network_type = "5G"
                        else:
                            # If mode is a number, default to 4G
                            network_type = "4G"
                        
                        rsrp = signal_data.get('rsrp', 'N/A')
                        
                        notification_title = f"Huawei Band Scanner - {network_type}"
                        notification_msg = f"Active band: {current_band}\nSignal: {rsrp}"
                        
                        toaster.show_toast(
                            notification_title,
                            notification_msg,
                            icon_path=None,
                            duration=5,
                            threaded=True
                        )
                    except Exception as e:
                        self.log_message(f"Failed to show connection notification: {str(e)}", log_type="detailed")
                
                # Update UI on main thread
                self.master.after(0, lambda: self.update_signal_ui(signal_data))
            else:
                self.log_message("Failed to fetch signal data", log_type="both")
        except Exception as e:
            self.log_message(f"Error refreshing signal: {str(e)}", log_type="both")
        finally:
            # Re-enable refresh button
            if hasattr(self, 'refresh_button'):
                self.master.after(0, lambda: self.refresh_button.config(state=tk.NORMAL))
    
    def update_signal_ui(self, signal_data):
        # Define mapping between signal_data keys and display keys
        field_mapping = {
            'rsrp': 'RSRP',
            'rsrq': 'RSRQ',
            'sinr': 'SINR',
            'band': 'BAND',
            'mode': 'NETWORK_TYPE',
            'plmn': 'CARRIER',
            'download': 'DOWNLOAD',
            'upload': 'UPLOAD'
        }
        
        # Log current signal values for debugging
        self.log_message(f"Updating signal UI with new data: " +
                       f"Band: {signal_data.get('band', 'N/A')}, " +
                       f"RSRP: {signal_data.get('rsrp', 'N/A')}", log_type="detailed")
        
        # Update each field if data exists
        for data_key, ui_key in field_mapping.items():
            if data_key in signal_data and ui_key in self.signal_info:
                # For network_type, convert numeric codes to user-friendly text
                if data_key == 'mode' and signal_data[data_key]:
                    mode_val = signal_data[data_key]
                    
                    # Convert numeric codes to user-friendly text
                    if mode_val == '101':
                        display_value = '5G NSA'
                    elif mode_val == '38':
                        display_value = 'NR/5G'
                    elif mode_val == '7':
                        display_value = '4G'
                    elif mode_val == '1011':
                        display_value = '4G+'
                    else:
                        # Try to make other network types user-friendly
                        network_types = {
                            "0": "No Service", "1": "GSM", "2": "GPRS", "3": "EDGE", "4": "WCDMA",
                            "5": "HSDPA", "6": "HSUPA", "7": "4G", "8": "TD-SCDMA", "9": "HSPA+",
                            "19": "LTE", "20": "LTE-CA (4G+)", "21": "5G NSA", "22": "5G SA"
                        }
                        display_value = network_types.get(str(mode_val), mode_val)
                    
                    self.signal_info[ui_key].set(display_value)
                else:
                    # Use data as is
                    display_value = signal_data[data_key]
                    
                # Handle empty or null values
                if display_value is None or display_value == '' or display_value == '--':
                    display_value = 'N/A'
                
                self.signal_info[ui_key].set(display_value)
        
        # Update the band checkboxes based on the current active band
        if 'band' in signal_data and signal_data['band'] and signal_data['band'] != '--' and signal_data['band'] != 'N/A':
            active_band = signal_data['band']
            self.log_message(f"Active band detected: {active_band}", log_type="detailed")
            
            # First, uncheck all bands
            for band, var in self.band_vars.items():
                var.set(False)
            
            # Try to find the band in our checkboxes with different formats
            found = False
            
            # Direct match
            if active_band in self.band_vars:
                self.band_vars[active_band].set(True)
                self.log_message(f"Updated band selection UI to show active band: {active_band}", log_type="detailed")
                found = True
            # If the band is a number without the "B" prefix, try with the prefix
            elif active_band.isdigit() and f"B{active_band}" in self.band_vars:
                self.band_vars[f"B{active_band}"].set(True)
                self.log_message(f"Updated band selection UI to show active band: B{active_band}", log_type="detailed")
                found = True
            # If the band has a "B" prefix, try without it
            elif active_band.startswith('B') and active_band[1:].isdigit() and active_band[1:] in self.band_vars:
                self.band_vars[active_band[1:]].set(True)
                self.log_message(f"Updated band selection UI to show active band: {active_band[1:]}", log_type="detailed")
                found = True
                
            if not found:
                self.log_message(f"Could not find checkbox for active band: {active_band} (not in available bands)", log_type="detailed")
                # Log available bands for debugging
                self.log_message(f"Available band checkboxes: {list(self.band_vars.keys())}", log_type="detailed")
        
        # Update RSRP color
        self.update_rsrp_color(signal_data.get('rsrp', 'N/A'))
    
    def update_rsrp_color(self, rsrp_value):
        """Update the RSRP display color based on signal strength"""
        try:
            # Extract the numeric value from the RSRP string (remove "dBm" if present)
            if isinstance(rsrp_value, str):
                if "dBm" in rsrp_value:
                    rsrp_value = rsrp_value.replace("dBm", "").strip()
                if rsrp_value == "N/A" or rsrp_value == "--":
                    # No valid RSRP value
                    return
                
            # Convert to float
            rsrp_float = float(rsrp_value)
            
            # Determine color based on RSRP value
            # Excellent: > -80 dBm
            # Good: -80 to -90 dBm
            # Fair: -90 to -100 dBm
            # Poor: < -100 dBm
            if rsrp_float >= -80:
                color = "#00CC00"  # Green
            elif rsrp_float >= -90:
                color = "#99CC00"  # Light green
            elif rsrp_float >= -100:
                color = "#CCCC00"  # Yellow
            else:
                color = "#CC0000"  # Red
                
            # Update the RSRP label color if it exists
            if hasattr(self, "signal_info") and "RSRP" in self.signal_info:
                if hasattr(self.signal_info["RSRP"], "config"):
                    # If it's a label
                    self.signal_info["RSRP"].config(foreground=color)
                # For StringVars we don't change colors, as they don't have a direct color property
        except Exception as e:
            # Silently fail if there's any error - this is non-essential functionality
            self.log_message(f"Error updating RSRP color: {str(e)}", log_type="detailed")
            pass

    def show_enhanced_optimisation_summary(self, results_4g, results_5g, recommended_results, report_path):
        """Show enhanced optimisation summary with separate 4G and 5G results"""
        # Get original band config
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(f"B{band}")
                
        # Create dialogue
        dialogue = tk.Toplevel(self.master)
        dialogue.title("Enhanced Optimisation Results")
        dialogue.geometry("800x600")  # Made wider and taller for more content
        dialogue.transient(self.master)
        dialogue.grab_set()
        
        # Create summary frame
        summary_frame = ttk.Frame(dialogue, padding="10")
        summary_frame.pack(fill=tk.BOTH, expand=True)
        
        # Header
        ttk.Label(summary_frame, text="Enhanced Optimisation Results", 
                  font=("TkDefaultFont", 12, "bold")).pack(pady=(0, 10))
        
        # Create text area for results
        text_area = tk.Text(summary_frame, wrap=tk.WORD, height=20)
        text_area.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        scroll = ttk.Scrollbar(summary_frame, command=text_area.yview)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)
        text_area.config(yscrollcommand=scroll.set)
        
        # Determine best overall option
        best_option = None
        best_speed = 0
        best_stability = 0
        
        if "4G" in recommended_results and "5G" in recommended_results:
            # Compare speeds and stability
            speed_4g = recommended_results["4G"]["download"]
            speed_5g = recommended_results["5G"]["download"]
            
            # Get stability metrics for recommended bands
            stability_4g = 0
            for band in results_4g:
                if f"B{band['band']}" in recommended_results["4G"]["bands"]:
                    stability_4g += float(band["signal_score"])
            stability_4g /= len(recommended_results["4G"]["bands"])
            
            stability_5g = 0
            for band in results_5g:
                if f"B{band['band']}" in recommended_results["5G"]["bands"]:
                    stability_5g += float(band["signal_score"])
            stability_5g /= len(recommended_results["5G"]["bands"])
            
            if speed_5g > speed_4g * 1.2 and stability_5g >= stability_4g * 0.8:  # 5G needs to be 20% faster and not more than 20% less stable
                best_option = "5G"
                best_speed = speed_5g
                best_stability = stability_5g
            else:
                best_option = "4G"
                best_speed = speed_4g
                best_stability = stability_4g
        elif "4G" in recommended_results:
            best_option = "4G"
            best_speed = recommended_results["4G"]["download"]
        elif "5G" in recommended_results:
            best_option = "5G"
            best_speed = recommended_results["5G"]["download"]
        
        # Add summary content
        summary = "📊 Optimisation Results Summary\n"
        summary += "═══════════════════════════\n\n"
        
        # 4G Results
        if results_4g:
            summary += "🔵 4G Results:\n"
            summary += "──────────────\n"
            if "4G" in recommended_results:
                rec_4g = recommended_results["4G"]
                summary += f"Recommended combination: {', '.join(rec_4g['bands'])}\n"
                summary += f"• Download: {rec_4g['download']:.2f} Mbps\n"
                summary += f"• Upload: {rec_4g['upload']:.2f} Mbps\n"
                summary += f"• Ping: {rec_4g['ping']:.1f} ms\n\n"
            
            summary += "Individual Band Performance:\n"
            for result in results_4g[:3]:  # Show top 3
                band = result['band']
                dl = result.get('download_mbps', 'Failed')
                ul = result.get('upload_mbps', 'Failed')
                ping = result.get('ping_ms', 'N/A')
                rsrp = result.get('rsrp', 'Unknown')
                sinr = result.get('sinr', 'Unknown')
                
                if dl != 'Failed':
                    summary += f"B{band}:\n"
                    summary += f"  Signal: RSRP {rsrp} dBm, SINR {sinr} dB\n"
                    summary += f"  Speed: ⬇️ {dl:.1f} Mbps, ⬆️ {ul:.1f} Mbps, 🔄 {ping:.0f}ms\n\n"
            
            summary += "\n"
        
        # 5G Results
        if results_5g:
            summary += "🟣 5G Results:\n"
            summary += "──────────────\n"
            if "5G" in recommended_results:
                rec_5g = recommended_results["5G"]
                summary += f"Recommended combination: {', '.join(rec_5g['bands'])}\n"
                summary += f"• Download: {rec_5g['download']:.2f} Mbps\n"
                summary += f"• Upload: {rec_5g['upload']:.2f} Mbps\n"
                summary += f"• Ping: {rec_5g['ping']:.1f} ms\n\n"
            
            summary += "Individual Band Performance:\n"
            for result in results_5g[:3]:  # Show top 3
                band = result['band']
                dl = result.get('download_mbps', 'Failed')
                ul = result.get('upload_mbps', 'Failed')
                ping = result.get('ping_ms', 'N/A')
                rsrp = result.get('rsrp', 'Unknown')
                sinr = result.get('sinr', 'Unknown')
                
                if dl != 'Failed':
                    summary += f"B{band}:\n"
                    summary += f"  Signal: RSRP {rsrp} dBm, SINR {sinr} dB\n"
                    summary += f"  Speed: ⬇️ {dl:.1f} Mbps, ⬆️ {ul:.1f} Mbps, 🔄 {ping:.0f}ms\n\n"
            
            summary += "\n"
        
        # Recommendation
        summary += "🎯 RECOMMENDATION:\n"
        summary += "═════════════════\n"
        if best_option:
            summary += f"Based on testing, {best_option} is recommended for optimal performance:\n\n"
            rec = recommended_results[best_option]
            summary += f"• Configuration: {', '.join(rec['bands'])}\n"
            summary += f"• Expected Download: {rec['download']:.2f} Mbps\n"
            summary += f"• Expected Upload: {rec['upload']:.2f} Mbps\n"
            summary += f"• Expected Ping: {rec['ping']:.1f} ms\n\n"
            
            if best_option == "4G":
                summary += "4G is recommended for better stability and consistent performance.\n"
            else:
                summary += "5G is recommended for higher speeds while maintaining acceptable stability.\n"
        
        summary += "\n⚠️ IMPORTANT: Use the buttons below to apply either the 4G or 5G configuration.\n"
        summary += "You can always switch back to your original settings using the Cancel button.\n\n"
        summary += f"A detailed report has been saved to:\n{report_path}"
        
        text_area.insert(tk.END, summary)
        text_area.config(state=tk.DISABLED)  # Make read-only
        
        # Button frame
        button_frame = ttk.Frame(dialogue, padding="10")
        button_frame.pack(fill=tk.X)
        
        def apply_4g():
            if "4G" not in recommended_results:
                messagebox.showwarning("Not Available", "No viable 4G configuration found.")
                return
                
            self.log_message(f"🔄 Applying 4G configuration: {', '.join(recommended_results['4G']['bands'])}", log_type="both")
            
            def apply_thread():
                success = apply_band_lock(
                    self.session or self.client, 
                    self.router_ip.get(), 
                    self.token, 
                    recommended_results['4G']['bands']
                )
                
                if success:
                    self.master.after(0, lambda: self.log_message("✅ 4G configuration applied successfully!", log_type="both"))
                    
                    # Update band selection checkboxes
                    for band_num, var in self.band_vars.items():
                        band_str = f"B{band_num}"
                        self.master.after(0, lambda bn=band_str, v=var: 
                            v.set(bn in recommended_results['4G']['bands']))
                    
                    self.master.after(5000, self.refresh_signal)
                else:
                    self.master.after(0, lambda: self.log_message("❌ Failed to apply 4G configuration.", log_type="both"))
            
            threading.Thread(target=apply_thread, daemon=True).start()
            dialogue.destroy()
        
        def apply_5g():
            if "5G" not in recommended_results:
                messagebox.showwarning("Not Available", "No viable 5G configuration found.")
                return
                
            self.log_message(f"🔄 Applying 5G configuration: {', '.join(recommended_results['5G']['bands'])}", log_type="both")
            
            def apply_thread():
                success = apply_band_lock(
                    self.session or self.client, 
                    self.router_ip.get(), 
                    self.token, 
                    recommended_results['5G']['bands']
                )
                
                if success:
                    self.master.after(0, lambda: self.log_message("✅ 5G configuration applied successfully!", log_type="both"))
                    
                    # Update band selection checkboxes
                    for band_num, var in self.band_vars.items():
                        band_str = f"B{band_num}"
                        self.master.after(0, lambda bn=band_str, v=var: 
                            v.set(bn in recommended_results['5G']['bands']))
                    
                    self.master.after(5000, self.refresh_signal)
                else:
                    self.master.after(0, lambda: self.log_message("❌ Failed to apply 5G configuration.", log_type="both"))
            
            threading.Thread(target=apply_thread, daemon=True).start()
            dialogue.destroy()
        
        def on_cancel():
            self.log_message("Optimisation cancelled. Restoring original band configuration.", log_type="both")
            
            if original_band_config:
                def restore_thread():
                    self.log_message(f"Restoring bands: {', '.join(original_band_config)}", log_type="detailed")
                    success, msg = apply_band_lock(
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token,
                        original_band_config
                    )
                    
                    if success:
                        self.master.after(0, lambda: self.log_message("✅ Original configuration restored", log_type="both"))
                        
                        # Update band selection checkboxes
                        for band_num, var in self.band_vars.items():
                            band_str = f"B{band_num}"
                            self.master.after(0, lambda bn=band_str, v=var: v.set(bn in original_band_config))
                        
                        self.master.after(5000, self.refresh_signal)
                    else:
                        self.master.after(0, lambda m=msg: self.log_message(f"❌ Failed to restore configuration: {m}", log_type="both"))
                
                threading.Thread(target=restore_thread, daemon=True).start()
            else:
                self.log_message("No previous configuration to restore", log_type="detailed")
            
            dialogue.destroy()
        
        def view_report():
            self.view_report(report_path)
        
        # Add buttons with appropriate states
        if "4G" in recommended_results:
            ttk.Button(button_frame, text="Apply 4G Configuration", command=apply_4g).pack(side=tk.LEFT, padx=5)
        if "5G" in recommended_results:
            ttk.Button(button_frame, text="Apply 5G Configuration", command=apply_5g).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="View Report", command=view_report).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=on_cancel).pack(side=tk.RIGHT, padx=5)
    
    def start_speedtest(self):
        """Run a standard speed test"""
        if not SPEEDTEST_AVAILABLE:
            self.log_message("speedtest-cli not installed. Install with: pip install speedtest-cli", log_type="both")
            return
        
        self.log_message("Starting speed test (this may take a minute)...", log_type="both")
        
        # Run in background thread to keep UI responsive
        def speedtest_thread():
            # Run the speed test
            result = run_speedtest()
            
            if result["success"]:
                dl = result["download"]
                ul = result["upload"]
                ping = result["ping"]
                server = result["server"]
                
                # Save speedtest results for use in update_signal_ui
                self.last_speedtest_time = time.time()
                self.last_speedtest_dl = dl
                self.last_speedtest_ul = ul
                
                # Update signal information with the new speed values
                self.signal_info["DOWNLOAD"].set(f"{dl:.2f} Mbps")
                self.signal_info["UPLOAD"].set(f"{ul:.2f} Mbps")
                
                # Log the speed test results
                self.log_message(f"Speed test results:\nDownload: {dl:.2f} Mbps\nUpload: {ul:.2f} Mbps\nPing: {ping:.2f} ms\nServer: {server}", log_type="both")
                
                # Also refresh the signal display with new speed values
                self.refresh_signal()
            else:
                self.log_message(f"Speed test failed: {result['message']}", log_type="both")
        
        threading.Thread(target=speedtest_thread, daemon=True).start()
    
    def show_about(self):
        """Show about dialog"""
        about_text = """Huawei Router Band Tool

A tool for optimising band selection on Huawei CPE Pro 2 routers.

Version: 1.0.2
Author: Rare
Licence: MIT"""
        
        messagebox.showinfo("About", about_text)

    def show_donation_dialog(self):
        """Show the donation dialog with PayPal button"""
        # Create donation dialog
        dialog = tk.Toplevel(self.master)
        dialog.title("Support the Project")
        dialog.geometry("400x300")
        dialog.transient(self.master)
        dialog.grab_set()
        
        # Add content
        ttk.Label(dialog, text="Support the Project", font=("TkDefaultFont", 14, "bold")).pack(pady=10)
        ttk.Label(dialog, text="If you find this tool helpful, please consider supporting its development.").pack(pady=5)
        
        # Create a text widget for the HTML content
        html_frame = ttk.Frame(dialog)
        html_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Use a label to show a "Click here to donate" message
        donate_label = ttk.Label(
            html_frame, 
            text="Click here to donate via PayPal", 
            cursor="hand2",
            foreground="blue"
        )
        donate_label.pack(pady=10)
        
        def open_paypal(event=None):
            webbrowser.open("https://www.paypal.com/ncp/payment/HLVZ82C6FKM2E")
        
        donate_label.bind("<Button-1>", open_paypal)
        
        # Add benefits text
        benefits_text = """Your support helps:
• Maintain and improve the application
• Add new features and optimizations
• Keep the project up to date
• Provide better documentation and support"""
        
        ttk.Label(dialog, text=benefits_text, justify=tk.LEFT).pack(pady=10, padx=20)
        
        # Close button
        ttk.Button(dialog, text="Close", command=dialog.destroy).pack(pady=10)

    def update_band_selection_ui(self):
        """Update band selection UI based on available bands"""
        # Debug the available_bands structure
        print(f"Available bands: {self.available_bands}")
        
        # Process available bands to ensure consistent format
        processed_4g_bands = []
        processed_5g_bands = []
        
        # Process 4G bands
        for band in self.available_bands["4G"]:
            if isinstance(band, str):
                if band.startswith('B'):
                    # Extract numeric part
                    try:
                        band_num = int(band[1:])
                        processed_4g_bands.append(band_num)
                    except ValueError:
                        # Skip invalid bands
                        continue
                else:
                    # Try to convert to int
                    try:
                        band_num = int(band)
                        processed_4g_bands.append(band_num)
                    except ValueError:
                        # Skip invalid bands
                        continue
            else:
                # Already a number
                processed_4g_bands.append(band)
        
        # Process 5G bands
        for band in self.available_bands["5G"]:
            if isinstance(band, str):
                if band.startswith('n'):
                    # Extract numeric part
                    try:
                        band_num = int(band[1:])
                        processed_5g_bands.append(band_num)
                    except ValueError:
                        # Skip invalid bands
                        continue
                else:
                    # Try to convert to int
                    try:
                        band_num = int(band)
                        processed_5g_bands.append(band_num)
                    except ValueError:
                        # Skip invalid bands
                        continue
            else:
                # Already a number
                processed_5g_bands.append(band)
        
        # Log available bands for debugging
        self.log_message(f"Processed 4G bands: {', '.join([f'B{b}' for b in processed_4g_bands])}", log_type="both")
        self.log_message(f"Processed 5G bands: {', '.join([f'n{b}' for b in processed_5g_bands])}", log_type="both")
        
        # Check if we have the band section tabs
        if hasattr(self, 'band_section_4g') and hasattr(self, 'band_section_5g'):
            # Update 4G bands tab
            # First, clear all existing widgets from the section
            for child in self.band_section_4g.winfo_children():
                child.destroy()
            
            # Sort band numbers numerically
            sorted_4g_bands = sorted(processed_4g_bands)
            
            # Create new checkboxes for available 4G bands
            # Group into rows of 4
            row = 0
            col = 0
            
            for band_num in sorted_4g_bands:
                band_name = f"B{band_num}"
                
                # Ensure the band variable exists
                if band_name not in self.band_vars:
                    self.band_vars[band_name] = tk.BooleanVar(value=False)
                
                # Add checkbox
                checkbox = ttk.Checkbutton(self.band_section_4g, text=band_name, 
                                          variable=self.band_vars[band_name])
                checkbox.grid(row=row, column=col, sticky=tk.W, padx=2, pady=1)
                col += 1
                if col >= 4:
                    col = 0
                    row += 1
            
            # Add control buttons at the bottom
            band_buttons_4g = ttk.Frame(self.band_section_4g)
            band_buttons_4g.grid(row=row+1, column=0, columnspan=4, pady=5)
            
            # Buttons removed as requested
            
            # Update 5G bands tab
            # First, clear all existing widgets from the section
            for child in self.band_section_5g.winfo_children():
                child.destroy()
            
            # Sort band numbers numerically
            sorted_5g_bands = sorted(processed_5g_bands)
            
            # Create new checkboxes for available 5G bands
            # Group into rows of 4
            row = 0
            col = 0
            
            for band_num in sorted_5g_bands:
                band_name = f"n{band_num}"
                
                # Ensure the band variable exists
                if band_name not in self.band_vars:
                    self.band_vars[band_name] = tk.BooleanVar(value=False)
                
                # Add checkbox
                checkbox = ttk.Checkbutton(self.band_section_5g, text=band_name, 
                                          variable=self.band_vars[band_name])
                checkbox.grid(row=row, column=col, sticky=tk.W, padx=2, pady=1)
                col += 1
                if col >= 4:
                    col = 0
                    row += 1
            
            # Add control buttons at the bottom
            band_buttons_5g = ttk.Frame(self.band_section_5g)
            band_buttons_5g.grid(row=row+1, column=0, columnspan=4, pady=5)
            
            # Buttons removed as requested
            
            self.log_message("Band selection updated with available bands", log_type="both")
        else:
            self.log_message("Could not find band selection UI - please restart the application", log_type="both")

    def get_recent_speedtest_results(self):
        # Return most recent speedtest results if available
        if hasattr(self, 'latest_speedtest_results') and self.latest_speedtest_results:
            return self.latest_speedtest_results
        return None

    def toggle_auto_refresh(self):
        """Toggle automatic signal refresh"""
        # Toggle the auto-refresh setting
        current_state = self.auto_refresh.get()
        self.auto_refresh.set(not current_state)
        new_state = self.auto_refresh.get()
        
        # Cancel any existing poll task first
        if hasattr(self, 'poll_status_task') and self.poll_status_task:
            self.master.after_cancel(self.poll_status_task)
            self.poll_status_task = None
            self.log_message("Cancelled existing polling task", log_type="detailed")
        
        # If enabling auto-refresh
        if new_state:
            self.log_message("Auto-refresh enabled. Signal will update every 30 seconds.", log_type="both")
            # Start the polling if we're connected
            if hasattr(self, 'is_connected') and self.is_connected:
                # Start a new polling task
                self.poll_status()
                self.log_message("Started polling task", log_type="detailed")
            else:
                self.log_message("Auto-refresh will begin after connecting to router", log_type="both")
        else:
            self.log_message("Auto-refresh disabled.", log_type="both")
    
    def poll_status(self):
        """Poll signal status at regular intervals"""
        try:
            # Check if we should still be polling
            if not (hasattr(self, 'is_connected') and self.is_connected and self.auto_refresh.get()):
                self.log_message("Polling stopped - disconnected or auto-refresh disabled", log_type="detailed")
                self.poll_status_task = None
                return
                
            # Refresh signal data
            self.refresh_signal()
            self.log_message("Auto-refreshed signal data", log_type="detailed")
            
            # Schedule the next refresh
            self.poll_status_task = self.master.after(30000, self.poll_status)
            
        except Exception as e:
            self.log_message(f"Error in polling task: {str(e)}", log_type="detailed")
            # Try to reschedule even if there was an error
            self.poll_status_task = self.master.after(30000, self.poll_status)

    def check_band_lock(self):
        """Check if current band matches user selection and reapply if needed"""
        try:
            # Get current selected bands from UI
            selected_bands = []
            for band, var in self.band_vars.items():
                if var.get():
                    selected_bands.append(band)
            
            if not selected_bands:
                return  # No bands selected to monitor
                
            # Get current band from signal info
            current_band = self.signal_info['BAND'].get() if 'BAND' in self.signal_info else ""
            if not current_band:
                return  # No current band info
                
            # Extract band numbers from current_band (e.g., "B7" -> ["B7"])
            # For carrier aggregation like "B7+B3", it would be ["B7", "B3"]
            current_bands = []
            if "+" in current_band:
                current_bands = [b.strip() for b in current_band.split("+")]
            else:
                current_bands = [current_band.strip()]
                
            # Check if any selected band is not in current bands
            selected_band_names = []
            for band in selected_bands:
                if band.startswith("B") or band.startswith("n"):
                    selected_band_names.append(band)
                else:
                    # Add prefix if needed
                    if int(band) > 100:  # 5G bands are typically > 100
                        selected_band_names.append(f"n{band}")
                    else:
                        selected_band_names.append(f"B{band}")
            
            band_mismatch = False
            # If user has selected specific bands and router is using different ones
            if selected_band_names and not any(sb in current_bands for sb in selected_band_names):
                band_mismatch = True
                
            if band_mismatch:
                message = f"Band lock changed: Router using {current_band} instead of {', '.join(selected_band_names)}"
                self.log_message(f"⚠️ {message}", log_type="both")
                self.log_message("🔄 Reapplying band lock...", log_type="both")
                
                # Show windows notification
                try:
                    toaster = ToastNotifier()
                    toaster.show_toast(
                        "Huawei Band Scanner",
                        message,
                        icon_path=None,
                        duration=5,
                        threaded=True
                    )
                except Exception as e:
                    self.log_message(f"Failed to show notification: {str(e)}", log_type="detailed")
                
                # Run in background thread to reapply bands
                def reapply_thread():
                    success = apply_band_lock(
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token,
                        selected_bands
                    )
                    
                    if success:
                        self.master.after(0, lambda: self.log_message("✅ Band lock reapplied successfully", log_type="both"))
                        self.master.after(5000, self.refresh_signal)
                        
                        # Show success notification
                        try:
                            toaster = ToastNotifier()
                            toaster.show_toast(
                                "Huawei Band Scanner",
                                "Band lock successfully reapplied",
                                icon_path=None,
                                duration=3,
                                threaded=True
                            )
                        except Exception as e:
                            pass  # Silently ignore notification errors
                    else:
                        self.master.after(0, lambda: self.log_message("❌ Failed to reapply band lock", log_type="both"))
                
                threading.Thread(target=reapply_thread, daemon=True).start()
        except Exception as e:
            self.log_message(f"Error in band monitoring: {str(e)}", log_type="detailed")

    def apply_band_selection(self):
        """Apply band selection to router"""
        selected_bands = []
        
        for band, var in self.band_vars.items():
            if var.get():
                selected_bands.append(band)
        
        if not selected_bands:
            self.log_message("No bands selected.", log_type="both")
            if hasattr(self, 'apply_bands_button'):
                self.apply_bands_button.config(state=tk.NORMAL)
            return
        
        # Store the selected bands for monitoring
        self.last_applied_bands = selected_bands.copy()
        
        band_list = ", ".join(selected_bands)
        self.log_message(f"Applying band selection: {band_list}...", log_type="both")
        
        # Run in background thread to keep UI responsive
        def apply_thread():
            try:
                success = apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, selected_bands)
                
                if success:
                    self.master.after(0, lambda: self.log_message("Band selection applied successfully. Changes may take up to 30 seconds to take effect.", log_type="both"))
                    
                    # Wait a moment for the router to apply changes, then refresh signal data
                    time.sleep(3)
                    self.master.after(0, self.refresh_signal)
                    
                    # Schedule additional refresh after a longer delay to ensure we get updated values
                    self.master.after(15000, self.refresh_signal)
                else:
                    self.master.after(0, lambda: self.log_message("Failed to apply band selection. Check connection.", log_type="both"))
            finally:
                # Re-enable button when done
                if hasattr(self, 'apply_bands_button'):
                    self.master.after(0, lambda: self.apply_bands_button.config(state=tk.NORMAL))
        
        threading.Thread(target=apply_thread, daemon=True).start()

    def apply_network_config(self):
        """Apply network aggregation configuration"""
        # Implementation will be added here
        pass

    def apply_network_mode(self):
        """Apply network mode selection"""
        # Implementation will be added here
        pass

    def toggle_all_bands(self, state, band_type):
        """Toggle all bands of a specific type (4G or 5G) to the given state"""
        try:
            # Process available bands to ensure consistent format
            processed_4g_bands = []
            processed_5g_bands = []
            
            # Process 4G bands
            for band in self.available_bands["4G"]:
                if isinstance(band, str):
                    if band.startswith('B'):
                        # Extract numeric part
                        try:
                            band_num = int(band[1:])
                            processed_4g_bands.append(band_num)
                        except ValueError:
                            # Skip invalid bands
                            continue
                    else:
                        # Try to convert to int
                        try:
                            band_num = int(band)
                            processed_4g_bands.append(band_num)
                        except ValueError:
                            # Skip invalid bands
                            continue
                else:
                    # Already a number
                    processed_4g_bands.append(band)
            
            # Process 5G bands
            for band in self.available_bands["5G"]:
                if isinstance(band, str):
                    if band.startswith('n'):
                        # Extract numeric part
                        try:
                            band_num = int(band[1:])
                            processed_5g_bands.append(band_num)
                        except ValueError:
                            # Skip invalid bands
                            continue
                    else:
                        # Try to convert to int
                        try:
                            band_num = int(band)
                            processed_5g_bands.append(band_num)
                        except ValueError:
                            # Skip invalid bands
                            continue
                else:
                    # Already a number
                    processed_5g_bands.append(band)
            
            # Set bands based on band type
            if band_type == "4G":
                band_names = [f"B{b}" for b in processed_4g_bands]
            else:  # 5G
                band_names = [f"n{b}" for b in processed_5g_bands]
            
            # Set all bands of the specified type to the given state
            for band_name in band_names:
                if band_name in self.band_vars:
                    self.band_vars[band_name].set(state)
            
            self.log_message(f"Set all {band_type} bands to {state}", log_type="both")
        except Exception as e:
            self.log_message(f"Error toggling bands: {str(e)}", log_type="both")

    def optimise(self):
        """Optimise band selection based on signal strength"""
        if not hasattr(self, 'is_connected') or not self.is_connected:
            self.log_message("⚠️ Not connected. Cannot optimise bands.", log_type="both")
            return
        
        # Disable buttons to prevent multiple clicks
        if hasattr(self, 'optimise_button'):
            self.optimise_button.config(state=tk.DISABLED)
        if hasattr(self, 'enhanced_optimise_button'):
            self.enhanced_optimise_button.config(state=tk.DISABLED)
        if hasattr(self, 'speedtest_button'):
            self.speedtest_button.config(state=tk.DISABLED)
        
        self.log_message("🔍 Starting band optimisation...", log_type="both")
        self.log_message("This process will test all available bands and recommend the best combination.", log_type="standard")
        
        # Save current band configuration before starting
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(band)
        
        self.log_message(f"Current band config saved: {', '.join(original_band_config) if original_band_config else 'No bands'}", log_type="detailed")
        
        # Define the optimization thread function
        def optimise_thread():
            try:
                # Test each band one by one
                results = {}
                
                # Test each band one by one - use available bands
                bands_to_test = self.available_bands["4G"] if hasattr(self, 'available_bands') else []
                
                # Track how many bands we've tested successfully
                successful_tests = 0
                
                for band in bands_to_test:
                    self.log_message(f"🔄 Testing band {band}...", log_type="standard")
                    self.log_message(f"Testing band {band}...", log_type="detailed")
                    
                    # Apply the band selection
                    try:
                        apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, [band])
                    except Exception as e:
                        if "Band not supported by this device" in str(e):
                            self.log_message(f"⚠️ Band {band} is not supported by this device", log_type="both")
                            results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True, "unsupported": True}
                            continue
                        else:
                            self.log_message(f"Error applying band lock: {str(e)}", log_type="both")
                            results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                            continue
                    
                    # Wait for connection to stabilize
                    time.sleep(12)
                    
                    # Refresh signal data
                    try:
                        if hasattr(self, 'client') and self.client:
                            # Using API client
                            signal_data = fetch_signal_data_api(self, self.client, self.router_ip.get())
                        else:
                            # Using web interface
                            signal_data = fetch_signal_data(self, self.session, self.router_ip.get(), self.token)
                    except Exception as e:
                        self.log_message(f"Error fetching signal data: {str(e)}", log_type="both")
                        results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                        continue
                    
                    if not signal_data:
                        self.log_message(f"⚠️ Failed to get signal data for band {band}", log_type="both")
                        results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                        continue
                    
                    # Send to detailed log
                    self.log_message(f"Band {band} signal data: {signal_data}", log_type="detailed")
                    
                    # Get signal metrics
                    try:
                        rsrp_str = signal_data.get("rsrp", "-120 dBm")
                        if isinstance(rsrp_str, str) and "dBm" in rsrp_str:
                            rsrp_str = rsrp_str.replace("dBm", "").strip()
                        rsrp_float = float(rsrp_str)
                        
                        sinr_str = signal_data.get("sinr", "0 dB")
                        if isinstance(sinr_str, str) and "dB" in sinr_str:
                            sinr_str = sinr_str.replace("dB", "").strip()
                        sinr_float = float(sinr_str)
                        
                        # Simple scoring algorithm considering RSRP and SINR
                        # RSRP range: -140 to -44 (higher is better)
                        # SINR range: -20 to 30 (higher is better)
                        
                        # Normalize RSRP to 0-100 range where 100 is best (-44dBm) and 0 is worst (-140dBm)
                        rsrp_norm = max(0, min(100, (rsrp_float + 140) / 96 * 100))
                        
                        # Normalize SINR to 0-100 range where 100 is best (30dB) and 0 is worst (-20dB)
                        sinr_norm = max(0, min(100, (sinr_float + 20) / 50 * 100))
                        
                        # Final score with more weight on RSRP (60%) than SINR (40%)
                        score = 0.6 * rsrp_norm + 0.4 * sinr_norm
                        
                        network_type = signal_data.get("mode", "4G")
                        
                        # Store results - use band string as key
                        results[band] = {
                            "score": score,
                            "rsrp": rsrp_float,
                            "sinr": sinr_float,
                            "network_type": network_type,
                            "failed": False
                        }
                        
                        # Show simple result in log
                        self.log_message(f"📊 Band {band}: RSRP {rsrp_float} dBm, SINR {sinr_float} dB, Score: {score:.1f}", log_type="standard")
                        
                        # Count successful test
                        successful_tests += 1
                    except Exception as e:
                        self.log_message(f"Error processing signal data for band {band}: {str(e)}", log_type="both")
                        results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                        continue
                
                # Check if we have any successful results
                if successful_tests == 0:
                    self.log_message("⚠️ No usable bands found. Try again or check connection.", log_type="both")
                    return
                
                # Generate report
                report_path = generate_report(results, "basic")

                # Find top bands
                sorted_bands = sorted(results.items(), key=lambda x: x[1]["score"], reverse=True)
                top_bands = [band for band, data in sorted_bands if data["score"] > 0][:3]
                
                if not top_bands:
                    self.log_message("⚠️ No usable bands found. Try again or check connection.", log_type="both")
                    return
                
                # Show optimisation summary dialogue
                self.master.after(0, lambda: self.show_optimisation_summary(top_bands, results, report_path))
                
                # Play notification sound
                self.master.bell()
            except Exception as e:
                self.log_message(f"Optimisation error: {str(e)}", log_type="both")
                # Try to restore the original band configuration
                try:
                    # Get original band config
                    original_band_config = []
                    for band, var in self.band_vars.items():
                        if var.get():
                            original_band_config.append(band)
                    
                    if original_band_config:
                        self.log_message(f"Restoring original band configuration: {', '.join(original_band_config)}", log_type="detailed")
                        apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, original_band_config)
                except Exception as restore_error:
                    self.log_message(f"Failed to restore original band configuration: {str(restore_error)}", log_type="detailed")
            finally:
                # Re-enable buttons when done
                if hasattr(self, 'optimise_button'):
                    self.master.after(0, lambda: self.optimise_button.config(state=tk.NORMAL))
                if hasattr(self, 'enhanced_optimise_button'):
                    self.master.after(0, lambda: self.enhanced_optimise_button.config(state=tk.NORMAL))
                if hasattr(self, 'speedtest_button'):
                    self.master.after(0, lambda: self.speedtest_button.config(state=tk.NORMAL))
        
        # Start the thread
        thread = threading.Thread(target=optimise_thread, daemon=True)
        thread.start()

    def enhanced_optimise(self):
        """Run enhanced optimisation with speed tests"""
        # Save current band configuration before starting
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(band)
        
        self.log_message(f"Current band config saved: {', '.join(original_band_config) if original_band_config else 'No bands'}", log_type="detailed")
        
        # Run optimisation in a background thread
        threading.Thread(target=self.enhanced_optimise_thread, daemon=True).start()

    def enhanced_optimise_thread(self):
        """Enhanced optimisation thread implementation"""
        try:
            # Store original band configuration
            original_band_config = []
            for band, var in self.band_vars.items():
                if var.get():
                    original_band_config.append(band)  # Already in the right format
            
            self.log_message(f"Current band config saved: {', '.join(original_band_config) if original_band_config else 'No bands'}", log_type="detailed")
            
            # Initialize results dictionaries with proper typing
            results_4g = {}
            results_5g = {}
            
            # Test 4G bands
            self.log_message("🔄 Testing 4G bands...", log_type="both")
            for band in self.available_bands["4G"]:
                try:
                    # Apply single band
                    success = apply_band_lock(
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token,
                        [band]
                    )
                    if not success:
                        self.log_message(f"Failed to apply band {band}, skipping", log_type="both")
                        continue
                    
                    # Wait for band to stabilize
                    time.sleep(12)
                    
                    # Get signal metrics
                    signal_data = fetch_signal_data(
                        self,
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token
                    )
                    
                    if not signal_data:
                        self.log_message(f"No signal data for band {band}, skipping", log_type="both")
                        continue
                    
                    # Run speedtest
                    speedtest_result = run_speedtest()
                    
                    # Get signal metrics
                    rsrp = signal_data.get("RSRP", "-120dBm")
                    if isinstance(rsrp, str) and "dBm" in rsrp:
                        rsrp = rsrp.replace("dBm", "")
                    rsrp_float = float(rsrp)
                    
                    sinr = signal_data.get("SINR", "0dB")
                    if isinstance(sinr, str) and "dB" in sinr:
                        sinr = sinr.replace("dB", "")
                    sinr_float = float(sinr)
                    
                    # Calculate signal quality score
                    rsrp_norm = max(0, min(100, (rsrp_float + 140) / 96 * 100))
                    sinr_norm = max(0, min(100, (sinr_float + 20) / 50 * 100))
                    signal_score = 0.6 * rsrp_norm + 0.4 * sinr_norm
                    
                    # Calculate speed score if speedtest successful
                    speed_score = 0
                    if speedtest_result["success"]:
                        dl_norm = min(100, speedtest_result["download"] / 2)  # Normalize to 0-100 (200 Mbps max)
                        ul_norm = min(100, speedtest_result["upload"])       # Normalize to 0-100 (100 Mbps max)
                        ping_norm = min(100, max(0, (1000 - speedtest_result["ping"]) / 10))  # Normalize to 0-100
                        speed_score = (dl_norm * 0.4) + (ul_norm * 0.4) + (ping_norm * 0.2)
                    
                    # Final score (60% signal, 40% speed if available)
                    final_score = signal_score if speed_score == 0 else (signal_score * 0.6 + speed_score * 0.4)
                    
                    # Store results
                    # Extract band number from band string (e.g. "B3" -> 3)
                    if band.startswith("B"):
                        band_num = int(band[1:])
                    else:
                        # Try to convert directly
                        band_num = int(band)
                    
                    results_4g[band_num] = {
                        "score": final_score,
                        "rsrp": rsrp_float,
                        "sinr": sinr_float,
                        "network_type": "4G",
                        "signal_score": signal_score,
                        "speed_score": speed_score,
                        "failed": False
                    }
                    
                    if speedtest_result["success"]:
                        results_4g[band_num].update({
                            "download_mbps": speedtest_result["download"],
                            "upload_mbps": speedtest_result["upload"],
                            "ping_ms": speedtest_result["ping"]
                        })
                    
                    # Show result in log
                    self.log_message(
                        f"📊 Band {band}: RSRP {rsrp_float} dBm, SINR {sinr_float} dB, "
                        f"Score: {final_score:.1f}" + 
                        (f", Speed: {speedtest_result['download']:.1f}/{speedtest_result['upload']:.1f} Mbps" 
                         if speedtest_result["success"] else ""),
                        log_type="both"
                    )
                    
                except Exception as e:
                    self.log_message(f"Error testing band {band}: {str(e)}", log_type="both")
                    continue
            
            # Test 5G bands if supported
            self.log_message("🔄 Testing 5G bands...", log_type="both")
            for band in self.available_bands["5G"]:
                try:
                    # Apply single band
                    success = apply_band_lock(
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token,
                        [band]
                    )
                    if not success:
                        self.log_message(f"Failed to apply band {band}, skipping", log_type="both")
                        continue
                    
                    # Wait for band to stabilize
                    time.sleep(12)
                    
                    # Get signal metrics
                    signal_data = fetch_signal_data(
                        self,
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token
                    )
                    
                    if not signal_data:
                        self.log_message(f"No signal data for band {band}, skipping", log_type="both")
                        continue
                    
                    # Run speedtest
                    speedtest_result = run_speedtest()
                    
                    # Get signal metrics
                    rsrp = signal_data.get("RSRP", "-120dBm")
                    if isinstance(rsrp, str) and "dBm" in rsrp:
                        rsrp = rsrp.replace("dBm", "")
                    rsrp_float = float(rsrp)
                    
                    sinr = signal_data.get("SINR", "0dB")
                    if isinstance(sinr, str) and "dB" in sinr:
                        sinr = sinr.replace("dB", "")
                    sinr_float = float(sinr)
                    
                    # Calculate signal quality score
                    rsrp_norm = max(0, min(100, (rsrp_float + 140) / 96 * 100))
                    sinr_norm = max(0, min(100, (sinr_float + 20) / 50 * 100))
                    signal_score = 0.6 * rsrp_norm + 0.4 * sinr_norm
                    
                    # Calculate speed score if speedtest successful
                    speed_score = 0
                    if speedtest_result["success"]:
                        dl_norm = min(100, speedtest_result["download"] / 4)  # Normalize to 0-100 (400 Mbps max for 5G)
                        ul_norm = min(100, speedtest_result["upload"] / 2)    # Normalize to 0-100 (200 Mbps max for 5G)
                        ping_norm = min(100, max(0, (1000 - speedtest_result["ping"]) / 10))  # Normalize to 0-100
                        speed_score = (dl_norm * 0.4) + (ul_norm * 0.4) + (ping_norm * 0.2)
                    
                    # Final score (60% signal, 40% speed if available)
                    final_score = signal_score if speed_score == 0 else (signal_score * 0.6 + speed_score * 0.4)
                    
                    # Store results
                    if band.startswith("n"):
                        band_num = int(band[1:])
                    else:
                        # Try to convert directly
                        band_num = int(band)
                    
                    results_5g[band_num] = {
                        "score": final_score,
                        "rsrp": rsrp_float,
                        "sinr": sinr_float,
                        "network_type": "5G",
                        "signal_score": signal_score,
                        "speed_score": speed_score,
                        "failed": False
                    }
                    
                    if speedtest_result["success"]:
                        results_5g[band_num].update({
                            "download_mbps": speedtest_result["download"],
                            "upload_mbps": speedtest_result["upload"],
                            "ping_ms": speedtest_result["ping"]
                        })
                    
                    # Show result in log
                    self.log_message(
                        f"📊 Band {band}: RSRP {rsrp_float} dBm, SINR {sinr_float} dB, "
                        f"Score: {final_score:.1f}" + 
                        (f", Speed: {speedtest_result['download']:.1f}/{speedtest_result['upload']:.1f} Mbps" 
                         if speedtest_result["success"] else ""),
                        log_type="both"
                    )
                    
                except Exception as e:
                    if "112003" in str(e):
                        self.log_message(f"Band {band} not supported by this device", log_type="both")
                    else:
                        self.log_message(f"Error testing band {band}: {str(e)}", log_type="both")
                    continue
            
            # Process results and find optimal combinations
            recommended_results = {}
            
            # Get top 2 4G bands
            if results_4g:
                sorted_4g = sorted(results_4g.items(), key=lambda x: x[1]["score"], reverse=True)
                top_4g_bands = [f"B{band}" for band, _ in sorted_4g[:2]]
                
                # Get the best 4G result data
                if len(sorted_4g) > 0:
                    best_4g = sorted_4g[0][1]
                    recommended_results["4G"] = {
                        "bands": top_4g_bands,
                        "download": best_4g.get("download_mbps", 0),
                        "upload": best_4g.get("upload_mbps", 0),
                        "ping": best_4g.get("ping_ms", 0),
                        "score": best_4g.get("score", 0)
                    }
            
            # Get best 5G band if available
            if results_5g:
                sorted_5g = sorted(results_5g.items(), key=lambda x: x[1]["score"], reverse=True)
                if sorted_5g:
                    top_5g_bands = [f"n{band}" for band, _ in sorted_5g[:1]]
                    
                    # Get the best 5G result data
                    best_5g = sorted_5g[0][1]
                    recommended_results["5G"] = {
                        "bands": top_5g_bands,
                        "download": best_5g.get("download_mbps", 0),
                        "upload": best_5g.get("upload_mbps", 0),
                        "ping": best_5g.get("ping_ms", 0),
                        "score": best_5g.get("score", 0)
                    }
            
            # Generate report
            report_path = generate_report({
                '4G_results': results_4g,
                '5G_results': results_5g,
                'recommended': recommended_results
            }, optimisation_type="enhanced")
            
            # Show results summary
            self.master.after(0, lambda: self.show_enhanced_optimisation_summary(
                results_4g, results_5g, recommended_results, report_path
            ))
            
            # Play notification sound
            self.master.bell()
            
        except Exception as e:
            self.log_message(f"Enhanced optimisation error: {str(e)}", log_type="both")
            # Attempt to restore original bands
            try:
                if original_band_config:
                    self.apply_band_selection(original_band_config)
            except Exception as restore_error:
                self.log_message(f"Failed to restore original bands: {str(restore_error)}", log_type="both")

    def apply_thread(self):
        try:
            # Collect selected bands
            selected_bands = {
                "4G": [band for band, var in self.band_vars_4g.items() if var.get()],
                "5G": [band for band, var in self.band_vars_5g.items() if var.get()]
            }
            
            # Add required verification
            if len(selected_bands["4G"]) == 0 and len(selected_bands["5G"]) == 0:
                self.master.after(0, lambda: self.log_message("Please select at least one band", log_type="error"))
                self.master.after(0, lambda: self.apply_bands_button.config(state=tk.NORMAL))
                return
            
            bands_list = selected_bands["4G"] + selected_bands["5G"]
            # Log the bands being applied
            bands_str = ", ".join(bands_list)
            self.master.after(0, lambda: self.log_message(f"Applying band selection: {bands_str}...", log_type="both"))
            
            # Apply band lock
            apply_band_lock(self.session, self.router_ip, self.token, selected_bands)
            
            # Update UI on success
            self.master.after(0, lambda: self.log_message("Band selection applied successfully. Changes may take up to 30 seconds to take effect.", log_type="both"))
            self.master.after(3000, self.refresh_signal)  # Refresh signal after 3 seconds
        except Exception as e:
            # Log error and re-enable button
            err_msg = f"Failed to apply band selection: {str(e)}"
            print(err_msg)
            self.master.after(0, lambda: self.log_message(err_msg, log_type="error"))
        finally:
            # Re-enable the apply button
            self.master.after(0, lambda: self.apply_bands_button.config(state=tk.NORMAL))

    def save_config(self):
        """Save configuration to file"""
        # Get current configuration
        config = {
            "router_ip": self.router_ip.get(),
            "username": self.username.get(),
            "password": self.password.get(),  # Save password as-is
            "auto_refresh": self.auto_refresh.get(),
            "monitor_bands": self.monitor_bands.get(),
            "minimize_to_tray": self.minimize_to_tray.get(),
            "auto_connect": self.auto_connect.get()
        }
        
        # Save to file
        try:
            with open("config.json", "w") as f:
                json.dump(config, f, indent=4, sort_keys=True)
            self.log_message("Configuration saved", log_type="detailed")
        except Exception as e:
            self.log_message(f"Failed to save configuration: {str(e)}", log_type="detailed")

    def setup_tray_icon(self):
        """Setup system tray icon and menu"""
        # Check if we already have a tray icon
        if self.tray_icon is not None:
            return
            
        try:
            # Create system tray icon
            if os.path.exists(self.icon_path):
                icon_image = Image.open(self.icon_path)
            else:
                # Create a simple icon if the icon file doesn't exist
                icon_image = Image.new('RGBA', (64, 64), color=(0, 120, 212, 255))
                
            # Create tray icon menu
            menu = (
                pystray.MenuItem('Show', self.show_window),
                pystray.MenuItem('Exit', self.exit_app)
            )
            
            # Create tray icon
            self.tray_icon = pystray.Icon("Huawei Band Scanner", icon_image, "Huawei Band Scanner", menu)
            
            # Start tray icon in a separate thread
            threading.Thread(target=self._run_tray_icon, daemon=True).start()
            
            # Bind window close event
            self.master.protocol("WM_DELETE_WINDOW", self.on_close)
            
            self.log_message("System tray icon setup completed", log_type="detailed")
        except Exception as e:
            self.log_message(f"Failed to setup system tray icon: {str(e)}", log_type="both")
            # Fallback to normal window behavior
            self.master.protocol("WM_DELETE_WINDOW", self.master.destroy)
            
    def _run_tray_icon(self):
        """Run the tray icon with error handling"""
        try:
            self.tray_icon.run()
        except TypeError as e:
            # Suppress Windows-specific errors
            error_msg = str(e)
            if any(err in error_msg for err in ["WPARAM is simple", "WNDPROC return value", "LRESULT"]):
                # Silently ignore these specific Windows-related errors
                pass
            else:
                print(f"Tray icon error: {str(e)}")
        except Exception as e:
            if "WNDPROC" in str(e) or "WPARAM" in str(e) or "LRESULT" in str(e):
                # Also ignore Windows-specific errors that might be raised as different exception types
                pass
            else:
                print(f"Tray icon error: {str(e)}")

    def show_window(self, icon=None, item=None):
        """Show the window from system tray"""
        self.master.deiconify()
        self.master.lift()
        self.master.focus_force()

    def hide_window(self):
        """Hide the window to system tray"""
        self.master.withdraw()
        
        # Show notification that app is still running
        try:
            toaster = ToastNotifier()
            toaster.show_toast(
                "Huawei Band Scanner",
                "Application is still running in the system tray",
                icon_path=None,
                duration=3,
                threaded=True
            )
        except Exception:
            pass

    def on_close(self):
        """Handle window close event"""
        if self.minimize_to_tray.get():
            # Hide to system tray
            self.hide_window()
        else:
            # Exit application
            self.exit_app()

    def exit_app(self, icon=None, item=None):
        """Properly exit the application, cleaning up resources"""
        try:
            # Stop any auto-refresh
            if hasattr(self, 'auto_refresh') and self.auto_refresh.get():
                self.toggle_auto_refresh()
                
            # Clean up tray icon if it exists
            if hasattr(self, 'tray_icon') and self.tray_icon is not None:
                try:
                    self.tray_icon.stop()
                except TypeError as e:
                    # Suppress WPARAM error on Windows
                    if "WPARAM is simple" not in str(e):
                        print(f"Error stopping tray icon: {str(e)}")
                except Exception as e:
                    print(f"Error stopping tray icon: {str(e)}")
                
            # Save configuration before exit
            self.save_config()
            
            # Exit the application
            self.master.destroy()
        except Exception as e:
            print(f"Error exiting: {str(e)}")
            # Force exit if cleanup fails
            import sys
            sys.exit(0)

# Add a new function for scanning available bands - around line 700-800
def scan_available_bands(session, ip, token):
    """Scan for available bands using the router's API"""
    available_bands = {
        "4G": [],
        "5G": []
    }
    
    # Check if we're using huawei-lte-api client
    if HUAWEI_API_AVAILABLE and isinstance(session, Client):
        try:
            # Get available bands from net_mode_list API
            net_mode_list = session.net.net_mode_list()
            
            # Log the raw response for debugging
            print(f"Net mode list response: {net_mode_list}")
            
            # Extract LTE bands - handle different response formats
            if "LTEBandList" in net_mode_list:
                lte_band_list = net_mode_list["LTEBandList"]
                
                # First, check if the data has LTEBand as a list
                if isinstance(lte_band_list, dict) and "LTEBand" in lte_band_list:
                    lte_bands = lte_band_list["LTEBand"]
                    
                    # Handle both list and single item cases
                    if not isinstance(lte_bands, list):
                        lte_bands = [lte_bands]
                    
                    # Process each LTEBand entry
                    for band_entry in lte_bands:
                        if isinstance(band_entry, dict) and "Name" in band_entry:
                            # Parse the name which contains band information
                            band_name = band_entry["Name"]
                            
                            # Look for patterns like "LTE BC1", "LTE BC3", etc.
                            if "LTE BC" in band_name:
                                for part in band_name.split("/"):
                                    if "LTE BC" in part:
                                        try:
                                            # Extract the band number from "LTE BCx"
                                            band_num = int(part.strip().replace("LTE BC", ""))
                                            available_bands["4G"].append(f"B{band_num}")
                                        except ValueError:
                                            # Skip if the band number isn't a valid integer
                                            pass
                
                # Also try the original approach if the new one didn't work
                if not available_bands["4G"] and isinstance(lte_band_list, str):
                    # Try to interpret as hex
                    try:
                        band_hex = int(lte_band_list, 16)
                        for band_num, band_mask in BAND_MAP.items():
                            if band_hex & band_mask:
                                available_bands["4G"].append(f"B{band_num}")
                    except ValueError:
                        # If not hex, try comma-separated format
                        if "," in lte_band_list:
                            for band in lte_band_list.split(","):
                                band = band.strip()
                                if band.startswith("B"):
                                    available_bands["4G"].append(band)
                                elif band.isdigit():
                                    available_bands["4G"].append(f"B{band}")
            
            # Extract 5G bands if available - similar nested structure handling
            if "NRBandList" in net_mode_list:
                nr_band_list = net_mode_list["NRBandList"]
                
                # Check if the data has NRBand as a list
                if isinstance(nr_band_list, dict) and "NRBand" in nr_band_list:
                    nr_bands = nr_band_list["NRBand"]
                    
                    # Handle both list and single item cases
                    if not isinstance(nr_bands, list):
                        nr_bands = [nr_bands]
                    
                    # Process each NRBand entry
                    for band_entry in nr_bands:
                        if isinstance(band_entry, dict) and "Name" in band_entry:
                            # Parse the name which contains band information
                            band_name = band_entry["Name"]
                            
                            # Look for patterns like "NR n1", "NR n78", etc.
                            if "NR n" in band_name:
                                for part in band_name.split("/"):
                                    if "NR n" in part:
                                        try:
                                            # Extract the band number from "NR nx"
                                            band_num = int(part.strip().replace("NR n", ""))
                                            available_bands["5G"].append(f"n{band_num}")
                                        except ValueError:
                                            # Skip if the band number isn't a valid integer
                                            pass
                
                # Try the original approach if the new one didn't work
                if not available_bands["5G"] and isinstance(nr_band_list, str):
                    try:
                        band_hex = int(nr_band_list, 16)
                        # 5G band mapping would be needed here
                        for band_num in [1, 3, 28, 41, 78, 79]:
                            available_bands["5G"].append(f"n{band_num}")
                    except ValueError:
                        if "," in nr_band_list:
                            for band in nr_band_list.split(","):
                                band = band.strip()
                                if band.startswith("n"):
                                    available_bands["5G"].append(band)
                                elif band.isdigit():
                                    available_bands["5G"].append(f"n{band}")
            
            # If no bands were detected, fall back to supported bands
            if not available_bands["4G"]:
                available_bands["4G"] = SUPPORTED_4G_BANDS
            if not available_bands["5G"]:
                available_bands["5G"] = SUPPORTED_5G_BANDS
                
            return available_bands
        except Exception as e:
            print(f"Error scanning bands via API: {str(e)}")
            # Fall back to default bands
            return {
                "4G": SUPPORTED_4G_BANDS,
                "5G": SUPPORTED_5G_BANDS
            }
    
    # Fall back to default bands
    return {
        "4G": SUPPORTED_4G_BANDS,
        "5G": SUPPORTED_5G_BANDS
    }

# Run GUI
if __name__ == "__main__":
    root = tk.Tk()
    app = BandOptimiserApp(root)
    root.mainloop()