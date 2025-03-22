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
from tkinter import ttk, messagebox, filedialog, scrolledtext
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
import pystray
from PIL import Image
import re
from io import BytesIO
import speedtest
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from statistics import mean, median

# Try to import win10toast for notifications, but provide a fallback if unavailable
NOTIFICATIONS_AVAILABLE = False
try:
    from win10toast import ToastNotifier
    NOTIFICATIONS_AVAILABLE = True
except ImportError:
    # Create a dummy ToastNotifier class that does nothing
    class ToastNotifier:
        def __init__(self):
            pass
        
        def show_toast(self, *args, **kwargs):
            pass

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

# Try to import huawei_lte_api if available
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

# 5G NR Band Map
NR_BAND_MAP = {
    1: 0x1,
    2: 0x2,
    3: 0x4,
    5: 0x10,
    7: 0x40,
    8: 0x80,
    20: 0x80000,
    28: 0x8000000,
    38: 0x2000000000,
    41: 0x10000000000, 
    66: 0x200000000000000,
    71: 0x4000000000000000,
    77: 0x100000000000000000,
    78: 0x200000000000000000,
    79: 0x400000000000000000
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
            return (client, None, f"Login Successful (API) - {device_info.get('devicename', '')} {device_info.get('HardwareVersion', '')}")
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
        return (None, None, f"Router at {ip} is not reachable. Check your connection and IP address.")
    
    try:
        # Fetch session token
        response = session.get(token_url, timeout=10)
        if response.status_code != 200:
            return (None, None, f"Failed to get CSRF token (Status: {response.status_code})")
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
                    return (session, token, f"Login Successful (Firmware: {firmware.text})")
            return (session, token, "Login Successful")
        else:
            return (None, None, f"Login Failed (Status: {response.status_code})")
    except requests.exceptions.ConnectTimeout:
        return (None, None, f"Connection to {ip} timed out. Verify the router is powered on and the IP is correct.")
    except requests.exceptions.ConnectionError:
        return (None, None, f"Cannot connect to {ip}. Check if the router is online and accessible.")
    except ET.ParseError:
        return (None, None, f"Received invalid XML from router. The device at {ip} may not be a Huawei router.")
    except Exception as e:
        error_type = type(e).__name__
        return (None, None, f"Connection Error ({error_type}): {str(e)}")

# Fetch Signal Data using huawei-lte-api library
def fetch_signal_data_api(self, client, ip):
    """Fetch signal data using the Huawei LTE API library"""
    try:
        # Verify client is valid before proceeding
        if client is None:
            self.log_message("API client is None, cannot fetch signal data", log_type="both")
            
            # Try to reconnect if we have credentials
            if hasattr(self, 'username') and hasattr(self, 'password') and self.username.get() and self.password.get():
                self.log_message("Attempting to reconnect with saved credentials", log_type="both")
                reconnection_successful = self.silent_reconnect(
                    self.router_ip.get(), 
                    self.username.get(), 
                    self.password.get(), 
                    getattr(self, 'use_api_value', True))
                    
                if reconnection_successful and self.client:
                    # If reconnection succeeded, retry with the new client
                    return fetch_signal_data_api(self, self.client, ip)
            
            # If we couldn't reconnect, raise an exception
            raise Exception("Invalid API client, reconnection attempt failed")
            
        # Get signal information
        signal_info = client.device.signal()
        
        # Initialize data dictionary
        signal_data = {}
        
        # Extract signal values (structure depends on the API version)
        if 'rsrp' in signal_info:
            signal_data['rsrp'] = signal_info.get('rsrp', '--')
        elif 'cell_id' in signal_info:
            for cell in signal_info['cell_id']:
                # Some CPE devices report RSRP for each cell - use the first one with valid data
                if cell.get('rsrp') and cell.get('rsrp') != '--':
                    signal_data['rsrp'] = cell.get('rsrp', '--')
                    signal_data['rsrq'] = cell.get('rsrq', '--')
                    signal_data['sinr'] = cell.get('sinr', '--')
                    break
        
        # If we don't have RSRP yet, try to get it from the first level
        if 'rsrp' not in signal_data or not signal_data['rsrp']:
            signal_data['rsrp'] = signal_info.get('rsrp', '--')
            signal_data['rsrq'] = signal_info.get('rsrq', '--')
            signal_data['sinr'] = signal_info.get('sinr', '--')
            
        # Make sure RSRQ and SINR are set even if they weren't in the original data
        if 'rsrq' not in signal_data or not signal_data['rsrq']:
            signal_data['rsrq'] = signal_info.get('rsrq', '--')
            # Try alternate field names for RSRQ that might be used
            if signal_data['rsrq'] == '--':
                for field in ['rsrq', 'RSRQ', 'rsqr', 'RSQR', 'RsrqRx0', 'RsrqRx1']:
                    if field in signal_info and signal_info[field] != '--':
                        signal_data['rsrq'] = signal_info[field]
                        break
        
        if 'sinr' not in signal_data or not signal_data['sinr']:
            signal_data['sinr'] = signal_info.get('sinr', '--')
            # Try alternate field names for SINR that might be used
            if signal_data['sinr'] == '--':
                for field in ['sinr', 'SINR', 'snr', 'SNR', 'SinrRx0', 'SinrRx1']:
                    if field in signal_info and signal_info[field] != '--':
                        signal_data['sinr'] = signal_info[field]
                        break
        
        # Get network mode and band info
        try:
            # Try to get detailed band information using different API endpoints
            
            # Method 1: Try to get from net.net_mode
            try:
                net_mode_info = client.net.net_mode()
                # Debug the response
                self.log_message(f"Net mode info: {net_mode_info}", log_type="detailed")
                
                if 'LTEBand' in net_mode_info:
                    # This is the hex value of the current band
                    lte_band_hex = net_mode_info.get('LTEBand', '--')
                    self.log_message(f"LTE band hex: {lte_band_hex}", log_type="detailed")
                    
                    # Convert hex to actual band numbers
                    if lte_band_hex != '--' and lte_band_hex != '0':
                        # Try to determine active bands from the hex value
                        try:
                            active_bands = []
                            lte_band_int = int(lte_band_hex, 16)
                            for band_num, band_hex in BAND_MAP.items():
                                if lte_band_int & band_hex:
                                    active_bands.append(f"B{band_num}")
                            
                            if active_bands:
                                signal_data['bands'] = ', '.join(active_bands)
                                signal_data['band'] = active_bands[0]  # Primary band is first one
                                signal_data['primary_band'] = active_bands[0]
                        except Exception as e:
                            self.log_message(f"Error parsing band hex: {str(e)}", log_type="detailed")
            except Exception as e:
                self.log_message(f"Error getting net_mode: {str(e)}", log_type="detailed")
            
            # Method 2: Try to get from device.signal
            if 'band' not in signal_data or signal_data['band'] == '--' or signal_data['band'] == 'LTE':
                if 'cell_id' in signal_info:
                    for cell in signal_info['cell_id']:
                        if 'band' in cell and cell['band'] != '--':
                            band_value = cell['band']
                            if not band_value.startswith('B') and band_value.isdigit():
                                band_value = f"B{band_value}"
                            signal_data['band'] = band_value
                            break
                
                # Try alternate fields that might contain band info
                band_fields = ['band', 'currentBand', 'activeBand', 'lte_band']
                for field in band_fields:
                    if field in signal_info and signal_info[field] != '--':
                        band_value = signal_info[field]
                        if not band_value.startswith('B') and band_value.isdigit():
                            band_value = f"B{band_value}"
                        signal_data['band'] = band_value
                        break
            
            # Method 3: Try to get from monitoring status
            if 'band' not in signal_data or signal_data['band'] == '--' or signal_data['band'] == 'LTE':
                try:
                    status_info = client.monitoring.status()
                    if 'CurrentNetworkType' in status_info:
                        signal_data['mode'] = status_info['CurrentNetworkType']
                    
                    # Try to extract band information from various fields
                    if 'CurrentBand' in status_info and status_info['CurrentBand'] != '--':
                        band_value = status_info['CurrentBand']
                        if not band_value.startswith('B') and band_value.isdigit():
                            band_value = f"B{band_value}"
                        signal_data['band'] = band_value
                        
                    # Try to get more detailed band info if available
                    band_info_fields = ['LTEBand', 'LTECA', 'CABands', 'LTECAInfo']
                    for field in band_info_fields:
                        if field in status_info and status_info[field] != '--':
                            signal_data['bands'] = status_info[field]
                            break
                except Exception as e:
                    self.log_message(f"Error getting monitoring status: {str(e)}", log_type="detailed")
                    
            # If we still don't have band info, try other methods
            if 'band' not in signal_data or signal_data['band'] == '--' or signal_data['band'] == 'LTE':
                # Get current PLMN for provider info
                plmn_info = client.net.current_plmn()
                signal_data['plmn_name'] = plmn_info.get('FullName', '--')
                
                # Try to get network mode info again to fill in missing data
                mode_info = client.net.network_mode()
                if 'NetworkMode' in mode_info and mode_info['NetworkMode'] != '--':
                    signal_data['mode'] = mode_info['NetworkMode']
                
                # Last resort - check if there's info from the basic monitoring status
                monitoring_status = client.monitoring.status()
                for key, value in monitoring_status.items():
                    if 'band' in key.lower() and value != '--':
                        band_value = value
                        if not band_value.startswith('B') and band_value.isdigit():
                            band_value = f"B{band_value}"
                        signal_data['band'] = band_value
                        break
            
            # If we have a bands list but no primary band, set it
            if 'bands' in signal_data and ('band' not in signal_data or signal_data['band'] == '--' or signal_data['band'] == 'LTE'):
                # Extract the first band from the list
                bands_list = signal_data['bands'].split(',')
                if bands_list:
                    signal_data['band'] = bands_list[0].strip()
            
            # Final fallback - at minimum we want to show if it's LTE/5G/etc.
            if 'mode' in signal_data and ('band' not in signal_data or signal_data['band'] == '--'):
                signal_data['band'] = signal_data['mode']
                
        except Exception as e:
            self.log_message(f"Error getting network info: {str(e)}", log_type="detailed")
        
        # Get traffic statistics if available
        try:
            traffic_stats = client.monitoring.traffic_statistics()
            
            # Save raw traffic stats to file for debugging
            debug_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug")
            if not os.path.exists(debug_dir):
                os.makedirs(debug_dir)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            debug_file = os.path.join(debug_dir, f"raw_traffic_stats_{timestamp}.json")
            with open(debug_file, 'w') as f:
                json.dump(traffic_stats, f, indent=4, default=str)
            self.log_message(f"Saved raw traffic stats to {debug_file}", log_type="detailed")
            
            # Log the raw values but don't update the UI display
            current_dl_rate = float(traffic_stats.get('CurrentDownloadRate', 0))
            current_ul_rate = float(traffic_stats.get('CurrentUploadRate', 0))
            
            # Log the raw traffic stats for reference, but don't set in signal_data
            self.log_message(f"Raw download rate: {current_dl_rate} bytes/s", log_type="detailed")
            self.log_message(f"Raw upload rate: {current_ul_rate} bytes/s", log_type="detailed")
            
            # Calculate and log values but don't assign to signal_data
            dl_mbps = (current_dl_rate * 8) / 1000000
            ul_mbps = (current_ul_rate * 8) / 1000000
            self.log_message(f"Current download rate: {dl_mbps:.2f} Mbps (not displayed in UI)", log_type="detailed")
            self.log_message(f"Current upload rate: {ul_mbps:.2f} Mbps (not displayed in UI)", log_type="detailed")
            
            # Don't assign values to signal_data as per user request
            # Only speedtest should update these values
            
        except Exception as e:
            self.log_message(f"Error getting traffic stats: {str(e)}", log_type="detailed")
        
        # Debug the signal data
        self.log_message(f"API signal data: {signal_data}", log_type="detailed")
        
        # Save processed signal data to file
        debug_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug")
        if not os.path.exists(debug_dir):
            os.makedirs(debug_dir)
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        debug_file = os.path.join(debug_dir, f"processed_signal_data_{timestamp}.json")
        with open(debug_file, 'w') as f:
            json.dump(signal_data, f, indent=4, default=str)
        self.log_message(f"Saved processed signal data to {debug_file}", log_type="detailed")
        
        return signal_data
    except Exception as e:
        self.log_message(f"Error in fetch_signal_data_api: {str(e)}", log_type="both")
        return None

# Unified fetch_signal_data function
def fetch_signal_data(self, session, ip, token):
    # Check if we're using huawei-lte-api client
    if hasattr(session, 'device') and session.__class__.__name__ == 'Client':
        try:
            return fetch_signal_data_api(self, session, ip)
        except Exception as e:
            error_str = str(e)
            self.log_message(f"Error fetching signal data from API: {error_str}", log_type="both")
            
            # Check for session timeout
            if "100003" in error_str or "No rights" in error_str or "needs login" in error_str:
                # Signal this is a session timeout to the caller
                self.session_timeout_detected = True
                
                # Try to silently reconnect if we have credentials
                if hasattr(self, 'username') and hasattr(self, 'password') and self.username.get() and self.password.get():
                    self.log_message("Session timeout detected in fetch_signal_data. Attempting to reconnect...", log_type="both")
                    reconnection_successful = self.silent_reconnect(ip, self.username.get(), self.password.get(), True)
                    
                    if reconnection_successful:
                        # If reconnection was successful, retry fetching data with the new session
                        try:
                            return fetch_signal_data(self, self.client, ip, self.token)
                        except Exception as retry_e:
                            self.log_message(f"Failed to fetch data after reconnection: {str(retry_e)}", log_type="both")
            
            return None
    
    # Otherwise use the session from requests
    try:
        # Get signal status
        signal_url = f"http://{ip}/api/device/signal"
        headers = {
            'Cookie': f'SessionID={token}',
            '__RequestVerificationToken': token
        }
        
        response = session.get(signal_url, headers=headers)
        
        # Check for session timeout in web response
        if response.status_code == 401 or "100003" in response.text or not response.ok or "error" in response.text.lower():
            error_str = response.text
            self.log_message(f"Error in web API response: {error_str}", log_type="both")
            
            # Check for session timeout markers
            if response.status_code == 401 or "100003" in error_str or "No rights" in error_str or "needs login" in error_str:
                # Signal this is a session timeout to the caller
                self.session_timeout_detected = True
                
                # Try to silently reconnect if we have credentials
                if hasattr(self, 'username') and hasattr(self, 'password') and self.username.get() and self.password.get():
                    self.log_message("Session timeout detected in fetch_signal_data. Attempting to reconnect...", log_type="both")
                    reconnection_successful = self.silent_reconnect(ip, self.username.get(), self.password.get(), False)
                    
                    if reconnection_successful:
                        # If reconnection was successful, retry fetching data with the new session
                        try:
                            return fetch_signal_data(self, self.session, ip, self.token)
                        except Exception as retry_e:
                            self.log_message(f"Failed to fetch data after reconnection: {str(retry_e)}", log_type="both")
            
            return None
        
        # Parse XML response
        signal_data = {}
        root = ET.fromstring(response.text)
        
        # Extract signal values
        signal_data['rsrp'] = root.find('.//rsrp').text if root.find('.//rsrp') is not None else '--'
        signal_data['rsrq'] = root.find('.//rsrq').text if root.find('.//rsrq') is not None else '--'
        signal_data['sinr'] = root.find('.//sinr').text if root.find('.//sinr') is not None else '--'
        signal_data['rssi'] = root.find('.//rssi').text if root.find('.//rssi') is not None else '--'
        signal_data['mode'] = root.find('.//mode').text if root.find('.//mode') is not None else '--'
        
        # Get additional information
        net_url = f"http://{ip}/api/net/current-plmn"
        response = session.get(net_url, headers=headers)
        
        if response.ok:
            root = ET.fromstring(response.text)
            signal_data['plmn'] = root.find('.//ShortName').text if root.find('.//ShortName') is not None else '--'
            
            # Get detailed band information for 5G
            try:
                bands = root.find('.//bands').text if root.find('.//bands') is not None else '--'
                primary_band = root.find('.//primary_band').text if root.find('.//primary_band') is not None else '--'
                signal_data['bands'] = bands
                signal_data['primary_band'] = primary_band
                
                # Log detailed band information
                self.log_message(f"Detailed band info - All bands: {bands}, Primary: {primary_band}", log_type="detailed")
            except Exception as e:
                self.log_message(f"Failed to parse detailed 5G band info: {str(e)}", log_type="detailed")
        
        # Get band info
        mon_url = f"http://{ip}/api/device/information"
        response = session.get(mon_url, headers=headers)
        
        if response.ok:
            root = ET.fromstring(response.text)
            signal_data['band'] = None
            
            # Try to find band through several possible XML paths
            for path in ['.//workmode', './/WorkMode', './/lteband', './/LTEBand', './/band']:
                band_elem = root.find(path)
                if band_elem is not None and band_elem.text:
                    signal_data['band'] = band_elem.text
                    break
            
            if not signal_data['band']:
                signal_data['band'] = '--'
        
        # Get recent speedtest results if available
        if hasattr(self, 'get_recent_speedtest_results'):
            recent_speedtest = self.get_recent_speedtest_results()
            if recent_speedtest:
                signal_data['download'] = f"{recent_speedtest.get('download', '0.00')} Mbps"
                signal_data['upload'] = f"{recent_speedtest.get('upload', '0.00')} Mbps"
        
        return signal_data
    except Exception as e:
        self.log_message(f"Error fetching signal data from web UI: {str(e)}", log_type="both")
        
        # Check for session timeout keywords in the exception
        error_str = str(e)
        if "100003" in error_str or "No rights" in error_str or "needs login" in error_str or "401" in error_str:
            # Signal this is a session timeout to the caller
            self.session_timeout_detected = True
            
            # Try to silently reconnect if we have credentials
            if hasattr(self, 'username') and hasattr(self, 'password') and self.username.get() and self.password.get():
                self.log_message("Session timeout detected in fetch_signal_data exception. Attempting to reconnect...", log_type="both")
                reconnection_successful = self.silent_reconnect(ip, self.username.get(), self.password.get(), False)
                
                if reconnection_successful:
                    # If reconnection was successful, retry fetching data with the new session
                    try:
                        return fetch_signal_data(self, self.session, ip, self.token)
                    except Exception as retry_e:
                        self.log_message(f"Failed to fetch data after reconnection: {str(retry_e)}", log_type="both")
        
        return None

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
        """Initialize the application"""
        super().__init__(master)
        self.master = master
        self.pack(fill=tk.BOTH, expand=True)
        
        # Initialize config
        self.router_ip = tk.StringVar(value="192.168.1.1")
        self.username = tk.StringVar(value="admin")
        self.password = tk.StringVar(value="")
        self.token = None
        self.session = None
        self.client = None
        self.is_connected = False
        self.api_restriction_warning_shown = False
        self.signal_update_interval = 30000  # 30 seconds
        self.poll_status_task = None  # Initialize to track auto-refresh
        self.refresh_in_progress = False
        self.poll_failure_count = 0
        
        # Initialize tray icon
        self.tray_icon = None
        self.icon_path = "assets/icon.ico"
        
        # Add variables for signal monitoring
        self.last_signal = {}
        self.notify_on_signal_change = tk.BooleanVar(value=True)
        self.signal_change_threshold = 3  # dB change that triggers notification
        
        # UI state variables
        self.status_var = tk.StringVar(value="Not Connected")
        self.auto_connect = tk.BooleanVar(value=False)
        self.use_api_lib = tk.BooleanVar(value=True)
        self.auto_refresh = tk.BooleanVar(value=True)
        self.monitor_bands = tk.BooleanVar(value=False)
        self.run_speed_on_start = tk.BooleanVar(value=False)
        self.minimize_to_tray = tk.BooleanVar(value=False)
        
        # Band selection variables
        self.band_vars = {}
        for band in SUPPORTED_4G_BANDS:
            band_name = f"B{band}"
            self.band_vars[band_name] = tk.BooleanVar(value=False)
        
        for band in SUPPORTED_5G_BANDS:
            band_name = f"n{band}"
            self.band_vars[band_name] = tk.BooleanVar(value=False)
        
        # Signal display variables
        self.signal_info = {
            'RSRP': tk.StringVar(value="--"),
            'RSRQ': tk.StringVar(value="--"),
            'SINR': tk.StringVar(value="--"),
            'BAND': tk.StringVar(value="--"),
            'NETWORK_TYPE': tk.StringVar(value="--"),
            'CARRIER': tk.StringVar(value="--"),
            'DOWNLOAD': tk.StringVar(value="--"),
            'UPLOAD': tk.StringVar(value="--")
        }
        
        # Initialize band variables for network aggregation
        self.upload_band_vars = {}
        self.download_band_vars = {}
        
        # Initialize the specific bands used in network aggregation
        for band_num in [1, 3, 7, 8]:  # These specific bands are used in the UI
            band = f"B{band_num}"
            self.upload_band_vars[band] = tk.BooleanVar(value=False)
            self.download_band_vars[band] = tk.BooleanVar(value=False)
        
        # Initialize available bands with defaults
        self.available_bands = {
            "4G": SUPPORTED_4G_BANDS,
            "5G": SUPPORTED_5G_BANDS
        }
        
        # Create the UI
        self.create_menu()
        self.create_main_frame()
        
        # Load config
        self.load_config()
        
        # Setup system tray
        self.setup_tray_icon()
        
        # Schedule a check for library version
        self.master.after(1000, self.check_library_version)
        
        # Auto-connect if enabled
        if self.auto_connect.get():
            self.master.after(1500, self.connect)

    def load_config(self):
        """Load configuration from file"""
        try:
            config = load_config()
            
            # Apply configuration to variables
            self.router_ip.set(config.get("router_ip", "192.168.1.1"))
            self.username.set(config.get("username", "admin"))
            self.password.set(config.get("password", ""))  # Load the password directly
            
            # Load other settings
            self.auto_connect.set(config.get("auto_connect", False))
            self.use_api_lib.set(config.get("use_api_lib", True))
            self.run_speed_on_start.set(config.get("run_speed_on_start", False))
            self.auto_refresh.set(config.get("auto_refresh", True))
            self.monitor_bands.set(config.get("monitor_bands", False))
            self.minimize_to_tray.set(config.get("minimize_to_tray", False))
            self.notify_on_signal_change.set(config.get("notify_on_signal_change", True))
            
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
        menu_bar = tk.Menu(self.master)
        self.master.config(menu=menu_bar)
        
        # Create File menu
        file_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="File", menu=file_menu)
        
        file_menu.add_command(label="Connect", command=self.connect)
        file_menu.add_command(label="Disconnect", command=self.disconnect)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_close)
        
        # Create Tools menu
        tools_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="Tools", menu=tools_menu)
        
        tools_menu.add_command(label="Speed Test", command=self.start_speedtest)
        tools_menu.add_command(label="Apply Band Selection", command=self.apply_band_selection)
        
        # Create Options menu
        options_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="Options", menu=options_menu)
        
        options_menu.add_checkbutton(label="Auto Refresh", variable=self.auto_refresh, 
                                    command=self.toggle_auto_refresh)
        options_menu.add_checkbutton(label="Monitor and Lock Bands", variable=self.monitor_bands,
                                    command=self.save_config)
        options_menu.add_checkbutton(label="Minimize to Tray on Close", variable=self.minimize_to_tray,
                                   command=self.save_config)  # Ensure this saves config when changed
        
        # Add notifications option
        options_menu.add_checkbutton(
            label="Signal Change Notifications", 
            variable=self.notify_on_signal_change, 
            command=self.save_config
        )
        
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
        
        # Create top section for router connection
        connection_frame = ttk.LabelFrame(main_frame, text="Router Connection", padding="5")
        connection_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Add error status label for displaying errors without popups
        self.error_display = ttk.Label(main_frame, text="", foreground="red", wraplength=780)
        self.error_display.pack(fill=tk.X, padx=5, pady=5)
        
        # Create grid for connection form
        ttk.Label(connection_frame, text="Router IP:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(connection_frame, textvariable=self.router_ip).grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        
        ttk.Label(connection_frame, text="Username:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(connection_frame, textvariable=self.username).grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
        
        ttk.Label(connection_frame, text="Password:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
        password_entry = ttk.Entry(connection_frame, textvariable=self.password, show="*")
        password_entry.grid(row=2, column=1, sticky=tk.W, padx=5, pady=5)
        
        # Options frame
        options_frame = ttk.Frame(connection_frame)
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
        self.connect_button = ttk.Button(connection_frame, text="Connect", command=self.connect)
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
            ("Primary Band:", "PRIMARY_BAND", "--"),
            ("All Bands:", "BAND", "--"),
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
            # Check if we're in the main thread
            is_main_thread = threading.current_thread() is threading.main_thread()
            
            # Function to actually update the UI
            def update_logs():
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
                except Exception as e:
                    # If we can't log to the UI, at least print to console
                    print(f"[{timestamp}] Error updating logs: {str(e)}")
            
            # If in main thread, update directly, otherwise use after
            if is_main_thread:
                update_logs()
            else:
                self.master.after(0, update_logs)
            
            # Also print to console for debugging (safe in any thread)
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
        """Connect to the router using the specified IP, username and password"""
        # Get values from UI
        ip = self.router_ip.get()
        username = self.username.get()
        password = self.password.get()
        use_api = self.use_api_lib.get()
        
        # Validate inputs
        if not ip:
            self.log_message("Please enter router IP address", log_type="both")
            self.error_display.config(text="Please enter router IP address")
            return
        
        if not username or not password:
            self.log_message("Please enter username and password", log_type="both")
            self.error_display.config(text="Please enter username and password")
            return
        
        # Update button text to indicate connecting, but keep it clickable
        self.connect_button.config(text="Connecting...")
        
        # Store values for use by worker thread
        self.log_message(f"Connecting to router at {ip}...", log_type="both")
        
        # Try to connect in a separate thread to keep UI responsive
        threading.Thread(target=lambda: self.connect_thread(ip, username, password, use_api), daemon=True).start()

    def disconnect(self):
        """Disconnect from the router"""
        if hasattr(self, 'is_connected') and self.is_connected:
            try:
                if hasattr(self, 'client') and self.client is not None:
                    # Close API connection
                    self.client.connection.close()
                    self.client = None
                elif hasattr(self, 'session') and self.session is not None:
                    # Logout from web session
                    logout_url = f"http://{self.router_ip.get()}/logout"
                    self.session.get(logout_url)
                    self.session = None
                
                # Clear token
                self.token = None
                
                # Cancel any polling tasks
                if hasattr(self, 'poll_status_task') and self.poll_status_task is not None:
                    self.master.after_cancel(self.poll_status_task)
                    self.poll_status_task = None
                
                # Update connection state
                self.is_connected = False
                
                # Update UI
                if hasattr(self, 'connect_button'):
                    self.connect_button.config(text="Connect", command=self.connect, state=tk.NORMAL)
                
                # Clear signal information
                for var in self.signal_info.values():
                    var.set("--")
                
                # Clear any error messages
                if hasattr(self, 'error_display'):
                    self.error_display.config(text="")
                
                self.log_message("Disconnected from router", log_type="both")
                
            except Exception as e:
                self.log_message(f"Error disconnecting: {str(e)}", log_type="both")
                if hasattr(self, 'error_display'):
                    self.error_display.config(text=f"Error disconnecting: {str(e)}")
        else:
            self.log_message("Not connected to any router", log_type="both")
            
    def connect_thread(self, ip, username, password, use_api):
        """Background thread for connecting to the router"""
        try:
            # Store credentials for auto-reconnect
            self.username.set(username)
            self.password.set(password)
            self.use_api_value = use_api  # This is used for silent reconnect
            
            # Initialize last activity timestamp
            if not hasattr(self, 'last_activity'):
                self.last_activity = time.time()
            
            # Try to connect to router
            result = login_to_router(ip, username, password, use_api)
            
            # Handle result on the main thread
            self.master.after(0, lambda: self.handle_connection_result(result, ip))
            
        except Exception as e:
            error_message = f"Error connecting to router: {str(e)}"
            self.log_message(f"❌ {error_message}", log_type="both")
            
            # Reset button on the main thread without disabling
            self.master.after(0, lambda: self.connect_button.config(text="Connect", command=self.connect))
            
            # Show error message
            self.master.after(0, lambda: self.error_display.config(text=error_message))
            self.master.after(0, lambda: messagebox.showerror("Connection Error", error_message))
    
    def handle_connection_result(self, result, ip):
        """Handle the result from the connection thread"""
        try:
            # Check if we got a valid result
            if result and len(result) >= 3:
                session_or_client = result[0]
                token = result[1]
                message = result[2]
                
                if session_or_client is not None:
                    # Connection successful
                    # Check which method was used and properly initialize
                    if self.use_api_lib.get() and HUAWEI_API_AVAILABLE and hasattr(session_or_client, 'device'):
                        # API client
                        self.client = session_or_client
                        self.session = None
                        self.log_message(f"Connected using Huawei LTE API (client initialized: {self.client is not None})", log_type="both")
                    else:
                        # Web session
                        self.session = session_or_client
                        self.client = None
                        self.log_message(f"Connected using web session (session initialized: {self.session is not None})", log_type="both")
                    
                    self.token = token
                    self.is_connected = True
                    
                    # Initialize polling failure counter
                    self.poll_failure_count = 0
                    
                    # Update UI
                    self.status_var.set("Connected")
                    self.connect_button.config(text="Disconnect", command=self.disconnect)
                    
                    # Start auto-refresh polling if enabled
                    if self.auto_refresh.get():
                        # Start session keepalive
                        self.start_session_keepalive()
                        
                        # Start polling
                        self.poll_status()
                        self.log_message("Auto-refresh enabled. Signal will update every 30 seconds.", log_type="both")
                        
                    # Scan for available bands
                    threading.Thread(target=self.update_band_selection_ui, daemon=True).start()
                    
                    # Refresh signal once after connection
                    threading.Thread(target=self.refresh_signal, daemon=True).start()
                    
                    # Clear any error messages
                    self.error_display.config(text="")
                else:
                    # Connection failed
                    error_message = message if message else "Unknown connection error"
                    self.log_message(f"❌ Connection failed: {error_message}", log_type="both")
                    self.status_var.set("Connection failed")
                    self.connect_button.config(text="Connect", command=self.connect)
                    self.error_display.config(text=error_message)
                    
                    # Show error dialog
                    messagebox.showerror("Connection Error", error_message)
            else:
                # Invalid result
                error_message = "Invalid connection result"
                if result and len(result) >= 3:
                    error_message = result[2] if result[2] else error_message
                    
                self.log_message(f"❌ {error_message}", log_type="both")
                self.status_var.set("Connection failed")
                self.connect_button.config(text="Connect", command=self.connect)
                self.error_display.config(text=error_message)
                
                # Show error dialog
                messagebox.showerror("Connection Error", error_message)
            
        except Exception as e:
            error_message = f"Error handling connection result: {str(e)}"
            self.log_message(f"❌ {error_message}", log_type="both")
            self.status_var.set("Connection error")
            self.connect_button.config(text="Connect", command=self.connect)
            self.error_display.config(text=error_message)
            
            # Show error dialog
            messagebox.showerror("Connection Error", error_message)

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

    def update_band_selection_ui(self):
        """Update band selection UI based on available bands"""
        # Debug the available_bands structure
        print(f"Available bands: {self.available_bands}")
        
        # Clear existing band_vars (checkbox states) to ensure stale selections are removed
        current_active_band = None
        if hasattr(self, 'signal_info') and 'BAND' in self.signal_info:
            current_active_band = self.signal_info['BAND'].get()
            if current_active_band == "--" or current_active_band == "N/A":
                current_active_band = None
        
        # Reset band variables - create a new dictionary
        self.band_vars = {}
        
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
                
                # Create unchecked checkbox variables by default
                is_active = False
                if current_active_band and band_name.upper() == current_active_band.upper():
                    is_active = True
                    
                self.band_vars[band_name] = tk.BooleanVar(value=is_active)
                
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
                
                # Create unchecked checkbox variables by default
                is_active = False
                if current_active_band and band_name.upper() == current_active_band.upper():
                    is_active = True
                    
                self.band_vars[band_name] = tk.BooleanVar(value=is_active)
                
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
            
            # If we have an active band, select it
            if current_active_band:
                self.select_active_band(current_active_band)
        else:
            self.log_message("Could not find band selection UI - please restart the application", log_type="both")

    def get_recent_speedtest_results(self):
        """Get the most recent speedtest results"""
        if hasattr(self, 'recent_speedtest'):
            return self.recent_speedtest
        return None

    def toggle_auto_refresh(self):
        """Toggle auto-refresh of signal data"""
        if self.auto_refresh.get():
            self.log_message("Auto-refresh enabled. Signal will update every 30 seconds.", log_type="both")
            
            # Start session keepalive mechanism
            self.start_session_keepalive()
            
            # Don't start polling if not connected yet
            if self.is_connected:
                self.poll_status()
            else:
                self.log_message("Auto-refresh will begin after connecting to router", log_type="both")
        else:
            self.log_message("Auto-refresh disabled", log_type="both")
            # Cancel any existing poll task
            if hasattr(self, 'poll_status_task') and self.poll_status_task:
                self.master.after_cancel(self.poll_status_task)
                self.poll_status_task = None
                
            # Cancel keepalive task
            if hasattr(self, 'keepalive_task') and self.keepalive_task:
                self.master.after_cancel(self.keepalive_task)
                self.keepalive_task = None
                
    def refresh_signal(self):
        """Refresh signal data"""
        if hasattr(self, 'refresh_in_progress') and self.refresh_in_progress:
            self.log_message("Refresh already in progress - skipping", log_type="detailed")
            return
            
        # Set flag to prevent multiple refreshes
        self.refresh_in_progress = True
        
        # Start refresh in a background thread
        self.log_message("Refreshing signal data...", log_type="detailed")
        threading.Thread(target=self.refresh_thread, daemon=True).start()

    def silent_reconnect(self, ip, username, password, use_api=True):
        """Attempt to reconnect to the router silently"""
        self.log_message(f"Silent reconnect attempt to {ip}... (API mode: {use_api})", log_type="detailed")
        
        # First, close any existing connections
        if hasattr(self, 'client') and self.client:
            try:
                self.client.user.logout()
            except:
                pass
            self.client = None
                
        if hasattr(self, 'session') and self.session:
            try:
                self.session.close()
            except:
                pass
            self.session = None
            self.token = None
        
        # Reset connection status
        self.is_connected = False
        
        # Attempt to reconnect
        try:
            # Use the global login_to_router function
            login_result = login_to_router(ip, username, password, use_api)
            
            if not login_result or not login_result[0]:
                self.log_message(f"Silent reconnect failed to {ip}", log_type="both")
                return False
                
            if use_api:
                # Set the client from the login result
                self.client = login_result[0]
                self.session = None
                self.token = None
            else:
                # Set the session and token from the login result
                self.client = None
                self.session = login_result[0]
                self.token = login_result[1]
                
            # Update connection state
            self.is_connected = True
            self.connection_type = "API" if use_api else "Web"
            self.reconnection_attempts = 0
            self.last_session_activity = time.time()
            self.session_timeout_detected = False
            
            # Reset polling if it was stopped
            if not hasattr(self, 'polling_task') or not self.polling_task:
                self.start_polling()
                
            # Ensure keepalive is active
            self.start_session_keepalive()
            
            self.log_message(f"Silent reconnect successful to {ip} using {self.connection_type}", log_type="both")
            return True
            
        except Exception as e:
            self.log_message(f"Silent reconnect error: {str(e)}", log_type="both")
            # Increment reconnection attempts counter
            if not hasattr(self, 'reconnection_attempts'):
                self.reconnection_attempts = 0
            self.reconnection_attempts += 1
            
            # Schedule another reconnection attempt if under the maximum attempts
            if self.reconnection_attempts < 5:
                self.log_message(f"Scheduling retry #{self.reconnection_attempts + 1} in 10 seconds...", log_type="detailed")
                self.master.after(10000, lambda: self.silent_reconnect(ip, username, password, use_api))
            else:
                self.log_message("Maximum reconnection attempts reached. Please reconnect manually.", log_type="both")
                # Reset the counter for next manual connection
                self.reconnection_attempts = 0
            return False

    def start_session_keepalive(self):
        """Start the session keepalive mechanism"""
        # Initialize the last activity timestamp if not already set
        if not hasattr(self, 'last_session_activity'):
            self.last_session_activity = time.time()
            
        # Cancel any existing keepalive task
        if hasattr(self, 'keepalive_task') and self.keepalive_task:
            self.master.after_cancel(self.keepalive_task)
        
        # Schedule the keepalive function - run every 30 seconds instead of 60 seconds
        self.keepalive_task = self.master.after(30000, self.session_keepalive)
    
    def session_keepalive(self):
        """Function to keep the router session alive"""
        try:
            if not self.is_connected or not self.auto_refresh.get():
                return
            
            current_time = time.time()
            # Send a keepalive request every 2 minutes instead of 4 minutes
            if hasattr(self, 'last_session_activity') and (current_time - self.last_session_activity) > 120:
                self.log_message("Sending session keepalive request", log_type="detailed")
                
                # Use a lightweight request to keep the session alive
                if hasattr(self, 'client') and self.client:
                    # For API client
                    try:
                        # Just retrieve basic status info
                        monitoring_status = self.client.monitoring.status()
                        # Update last activity time
                        self.last_session_activity = time.time()
                        # Log success with device info
                        device_name = monitoring_status.get('DeviceName', 'Unknown')
                        self.log_message(f"Keepalive successful (API) - Device: {device_name}", log_type="detailed")
                    except Exception as e:
                        error_str = str(e)
                        if "100003" in error_str or "No rights" in error_str or "needs login" in error_str:
                            # Session already expired, attempt reconnection immediately
                            self.log_message("Session expired during keepalive check. Reconnecting...", log_type="both")
                            self.session_timeout_detected = True
                            # Attempt reconnection
                            if hasattr(self, 'username') and hasattr(self, 'password'):
                                reconnect_result = self.silent_reconnect(
                                    self.router_ip.get(), 
                                    self.username.get(), 
                                    self.password.get(), 
                                    True)
                                if reconnect_result:
                                    self.log_message("Reconnected successfully during keepalive", log_type="both")
                                else:
                                    self.log_message("Failed to reconnect during keepalive", log_type="both")
                        else:
                            self.log_message(f"Keepalive request failed: {error_str}", log_type="detailed")
                elif hasattr(self, 'session') and self.session:
                    # For web session
                    try:
                        ip = self.router_ip.get()
                        headers = {
                            'Cookie': f'SessionID={self.token}',
                            '__RequestVerificationToken': self.token
                        }
                        # Just get a basic status page
                        response = self.session.get(f"http://{ip}/api/monitoring/status", headers=headers)
                        if response.ok:
                            self.last_session_activity = time.time()
                            self.log_message("Keepalive successful (Web)", log_type="detailed")
                        elif "100003" in response.text:
                            # Session already expired, attempt reconnection immediately
                            self.log_message("Session expired during keepalive check. Reconnecting...", log_type="both")
                            self.session_timeout_detected = True
                            # Attempt reconnection
                            reconnect_result = self.silent_reconnect(
                                self.router_ip.get(), 
                                self.username.get(), 
                                self.password.get(), 
                                False)
                            if reconnect_result:
                                self.log_message("Reconnected successfully during keepalive", log_type="both")
                            else:
                                self.log_message("Failed to reconnect during keepalive", log_type="both")
                        else:
                            # Response not OK, but not session timeout - log it
                            self.log_message(f"Keepalive request returned status {response.status_code}: {response.text[:100]}", log_type="detailed")
                    except Exception as e:
                        self.log_message(f"Keepalive request failed: {str(e)}", log_type="detailed")
                        # Check if this is a connection error and attempt reconnection
                        if "Connection" in str(e) or "Timeout" in str(e):
                            self.log_message("Connection error during keepalive. Attempting reconnect...", log_type="both")
                            reconnect_result = self.silent_reconnect(
                                self.router_ip.get(), 
                                self.username.get(), 
                                self.password.get(), 
                                False)
                            if reconnect_result:
                                self.log_message("Reconnected successfully after connection error", log_type="both")
                else:
                    # No valid client or session
                    self.log_message("No valid connection found during keepalive. Attempting reconnect...", log_type="both")
                    reconnect_result = self.silent_reconnect(
                        self.router_ip.get(), 
                        self.username.get(), 
                        self.password.get(), 
                        True) # Default to API mode for reconnect
                    if reconnect_result:
                        self.log_message("Reconnected successfully after missing connection", log_type="both")
            else:
                # Add a more frequent but lighter status check
                if hasattr(self, 'client') and self.client:
                    try:
                        # Just check a very basic API endpoint to maintain activity
                        self.client.device.basic_information()
                        # Don't update last_session_activity here - we only track the full status checks
                    except Exception as e:
                        error_str = str(e)
                        if "100003" in error_str or "No rights" in error_str or "needs login" in error_str:
                            # Session already expired, attempt reconnection immediately
                            self.log_message("Session expired during light check. Reconnecting...", log_type="detailed")
                            self.session_timeout_detected = True
                            # Attempt reconnection
                            self.silent_reconnect(
                                self.router_ip.get(), 
                                self.username.get(), 
                                self.password.get(), 
                                True)
                elif hasattr(self, 'session') and self.session:
                    # Do a light check for web session too
                    try:
                        ip = self.router_ip.get()
                        headers = {
                            'Cookie': f'SessionID={self.token}',
                            '__RequestVerificationToken': self.token
                        }
                        # Get a very lightweight endpoint
                        response = self.session.get(f"http://{ip}/api/device/basic_information", headers=headers)
                        if not response.ok and "100003" in response.text:
                            # Session expired, reconnect
                            self.log_message("Session expired during light web check. Reconnecting...", log_type="detailed")
                            self.session_timeout_detected = True
                            self.silent_reconnect(
                                self.router_ip.get(), 
                                self.username.get(), 
                                self.password.get(), 
                                False)
                    except Exception:
                        # Ignore errors in the light check
                        pass
        except Exception as e:
            self.log_message(f"Error in keepalive: {str(e)}", log_type="detailed")
        finally:
            # Reschedule the keepalive - make it more frequent (30 seconds instead of 60)
            self.keepalive_task = self.master.after(30000, self.session_keepalive)
    
    def poll_status(self):
        """Poll signal status at regular intervals"""
        try:
            # Check if we should still be polling
            if not self.is_connected:
                self.log_message("Polling stopped - disconnected", log_type="detailed")
                self.poll_status_task = None
                return
                
            if not self.auto_refresh.get():
                self.log_message("Polling stopped - auto-refresh disabled", log_type="detailed")
                self.poll_status_task = None
                return
            
            # Add failure counter logic to prevent infinite retries
            if not hasattr(self, 'poll_failure_count'):
                self.poll_failure_count = 0
                
            # Check if session timeout was detected
            if hasattr(self, 'session_timeout_detected') and self.session_timeout_detected:
                self.log_message("Session timeout detected. Attempting auto-reconnect...", log_type="both")
                reconnect_result = self.auto_reconnect()
                if reconnect_result:
                    self.session_timeout_detected = False
                    self.poll_failure_count = 0
                    self.log_message("Auto-reconnect successful", log_type="both")
                else:
                    self.log_message("Auto-reconnect failed", log_type="both")
                    self.poll_failure_count += 1
            
            # Limit consecutive failures
            if hasattr(self, 'poll_failure_count') and self.poll_failure_count >= 5:
                error_message = "Auto-refresh disabled after 5 consecutive failures. The router may be unresponsive."
                self.log_message(error_message, log_type="both")
                self.auto_refresh.set(False)
                
                # Update error display in UI
                self.master.after(0, lambda: self.error_display.config(text=error_message))
                
                # Show a notification
                try:
                    if NOTIFICATIONS_AVAILABLE:
                        toaster = ToastNotifier()
                        toaster.show_toast(
                            "Auto-refresh Disabled",
                            error_message,
                            icon_path=None,
                            duration=5,
                            threaded=True
                        )
                except Exception:
                    pass
                
                self.poll_status_task = None
                return
            
            # Refresh signal data
            try:
                self.refresh_signal()
                self.log_message("Auto-refreshed signal data", log_type="detailed")
                # Reset failure counter on success
                self.poll_failure_count = 0
                # Also reset session timeout flag
                if hasattr(self, 'session_timeout_detected'):
                    self.session_timeout_detected = False
            except Exception as e:
                error_str = str(e)
                # Check if this is a session timeout error
                if "No rights" in error_str or "needs login" in error_str or "100003" in error_str or "login required" in error_str:
                    self.log_message("Session timeout detected in polling, will attempt reconnect", log_type="detailed")
                    self.session_timeout_detected = True
                
                # Increment failure counter
                self.poll_failure_count += 1
                self.log_message(f"Error in auto-refresh ({self.poll_failure_count}/5): {str(e)}", log_type="both")
            
        except Exception as e:
            self.log_message(f"Error in polling task: {str(e)}", log_type="both")
        finally:
            # Always schedule the next refresh, regardless of current state
            # This ensures continuous polling as long as auto-refresh is enabled
            if self.is_connected and self.auto_refresh.get():
                try:
                    # Use a shorter interval if we're waiting for reconnection
                    interval = 5000 if hasattr(self, 'session_timeout_detected') and self.session_timeout_detected else self.signal_update_interval
                    self.poll_status_task = self.master.after(interval, self.poll_status)
                    self.log_message(f"Scheduled next poll in {interval/1000} seconds", log_type="detailed")
                except Exception as e:
                    self.log_message(f"Error scheduling next poll: {str(e)}", log_type="detailed")
            else:
                self.poll_status_task = None
    
    def start_speedtest(self):
        """Run a speed test and display the results"""
        if not hasattr(self, 'is_connected') or not self.is_connected:
            self.log_message("Cannot run speedtest: Not connected to router", log_type="both")
            messagebox.showwarning("Not Connected", "Please connect to the router first.")
            return
        
        # Disable the speedtest button while running
        if hasattr(self, 'speedtest_button'):
            self.speedtest_button.config(state=tk.DISABLED)
        
        self.log_message("Starting speed test. This may take a minute...", log_type="both")
        
        # Run in a separate thread to prevent UI freezing
        def speedtest_thread():
            try:
                # Run the speedtest
                result = run_speedtest()
                
                if result["success"]:
                    # Format the results
                    download = result["download"]
                    upload = result["upload"]
                    ping = result["ping"]
                    
                    # Store results for future reference
                    self.recent_speedtest = result
                    
                    # Update UI with results
                    success_message = f"✅ Speed test complete: ⬇️ {download:.2f} Mbps | ⬆️ {upload:.2f} Mbps | Ping: {ping} ms"
                    self.master.after(0, lambda: self.log_message(success_message, log_type="both"))
                    
                    # Show a result dialog
                    self.master.after(0, lambda: messagebox.showinfo("Speed Test Results", 
                        f"Download: {download:.2f} Mbps\nUpload: {upload:.2f} Mbps\nPing: {ping} ms"))
                    
                    # Update signal info if available
                    if hasattr(self, 'signal_info') and 'DOWNLOAD' in self.signal_info and 'UPLOAD' in self.signal_info:
                        self.master.after(0, lambda: self.signal_info['DOWNLOAD'].set(f"{download:.2f} Mbps"))
                        self.master.after(0, lambda: self.signal_info['UPLOAD'].set(f"{upload:.2f} Mbps"))
                else:
                    error_message = f"❌ Speed test failed: {result.get('error', 'Unknown error')}"
                    self.master.after(0, lambda: self.log_message(error_message, log_type="both"))
                    self.master.after(0, lambda: messagebox.showerror("Speed Test Failed", error_message))
            
            except Exception as e:
                error_message = f"Speed test error: {str(e)}"
                self.master.after(0, lambda: self.log_message(f"❌ {error_message}", log_type="both"))
                self.master.after(0, lambda: messagebox.showerror("Speed Test Error", error_message))
            
            finally:
                # Re-enable the speedtest button
                if hasattr(self, 'speedtest_button'):
                    self.master.after(0, lambda: self.speedtest_button.config(state=tk.NORMAL))
        
        # Start the thread
        threading.Thread(target=speedtest_thread, daemon=True).start()
    
    def apply_network_config(self):
        """Apply network aggregation configuration"""
        # Implementation will be added here
        pass

    def apply_network_mode(self):
        """Apply network mode selection"""
        # Implementation will be added here
        pass

    def toggle_all_bands(self, state, band_type="all"):
        """Toggle all bands of a specific type (4G or 5G) to the given state"""
        try:
            # Process available bands to ensure consistent format
            processed_4g_bands = []
            processed_5g_bands = []
            
            # Process 4G bands
            for band in self.available_bands.get("4G", []):
                if isinstance(band, str) and band.startswith("B"):
                    processed_4g_bands.append(band)
                elif isinstance(band, int) or (isinstance(band, str) and band.isdigit()):
                    processed_4g_bands.append(f"B{band}")
            
            # Process 5G bands
            for band in self.available_bands.get("5G", []):
                if isinstance(band, str) and band.startswith("n"):
                    processed_5g_bands.append(band)
                elif isinstance(band, int) or (isinstance(band, str) and band.isdigit()):
                    processed_5g_bands.append(f"n{band}")
            
            # Update checkboxes based on the band type
            if band_type == "all" or band_type == "4G":
                for band in processed_4g_bands:
                    if band in self.band_vars:
                        self.band_vars[band].set(state)
            
            if band_type == "all" or band_type == "5G":
                for band in processed_5g_bands:
                    if band in self.band_vars:
                        self.band_vars[band].set(state)
                        
            self.log_message(f"{'Selected' if state else 'Cleared'} all {band_type} bands", log_type="both")
            
        except Exception as e:
            self.log_message(f"Error toggling bands: {str(e)}", log_type="both")
            
    def apply_band_selection(self):
        """Apply the currently selected bands to the router"""
        if not hasattr(self, 'is_connected') or not self.is_connected:
            self.log_message("⚠️ Not connected to router. Cannot apply band selection.", log_type="both")
            return
            
        # Disable apply button while working
        if hasattr(self, 'apply_bands_button'):
            self.apply_bands_button.config(state=tk.DISABLED)
            
        try:
            # Collect selected bands
            selected_bands = []
            for band, var in self.band_vars.items():
                if var.get():
                    selected_bands.append(band)
                    
            if not selected_bands:
                self.log_message("⚠️ No bands selected. Please select at least one band.", log_type="both")
                if hasattr(self, 'apply_bands_button'):
                    self.apply_bands_button.config(state=tk.NORMAL)
                return
                
            self.log_message(f"🔄 Applying band selection: {', '.join(selected_bands)}", log_type="both")
            
            # Start the apply operation in a background thread
            threading.Thread(target=lambda: self.apply_band_thread(selected_bands), daemon=True).start()
            
        except Exception as e:
            self.log_message(f"❌ Error preparing band selection: {str(e)}", log_type="both")
            if hasattr(self, 'apply_bands_button'):
                self.apply_bands_button.config(state=tk.NORMAL)
                
    def apply_band_thread(self, selected_bands):
        """Background thread for applying band selection"""
        try:
            # Apply the band lock
            apply_band_lock(
                self.session or self.client,
                self.router_ip.get(),
                self.token,
                selected_bands
            )
            
            # Update UI on success
            self.master.after(0, lambda: self.log_message("✅ Band selection applied successfully!", log_type="both"))
            
            # Refresh signal after a short delay
            self.master.after(5000, self.refresh_signal)
            
        except Exception as e:
            # Handle errors
            error_message = f"❌ Error applying band selection: {str(e)}"
            self.master.after(0, lambda: self.log_message(error_message, log_type="both"))
            
        finally:
            # Re-enable the apply button
            if hasattr(self, 'apply_bands_button'):
                self.master.after(0, lambda: self.apply_bands_button.config(state=tk.NORMAL))

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
                            error_message = f"Error applying band lock: {str(e)}"
                            self.log_message(error_message, log_type="both")
                            results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                            continue
                    
                    # Wait for connection to stabilize
                    # Increased from 5 to 10 seconds for better 5G stabilization
                    time.sleep(10)
                    
                    # Refresh signal data
                    try:
                        if hasattr(self, 'client') and self.client:
                            # Using API client
                            signal_data = fetch_signal_data_api(self, self.client, self.router_ip.get())
                        else:
                            # Using web client
                            signal_data = fetch_signal_data(self, self.session, self.router_ip.get(), self.token)
                        
                        # Check if we got valid signal data
                        if not signal_data or not isinstance(signal_data, dict):
                            self.log_message(f"❌ Failed to get signal data for band {band}", log_type="both")
                            results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                            continue
                    except Exception as e:
                        self.log_message(f"❌ Error getting signal data: {str(e)}", log_type="both")
                        results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                        continue
                    
                    # Extract RSRP value
                    try:
                        rsrp_str = signal_data.get("rsrp", "-120 dBm")
                        if isinstance(rsrp_str, str) and "dBm" in rsrp_str:
                            rsrp_str = rsrp_str.replace("dBm", "").strip()
                        rsrp = float(rsrp_str)
                    except (ValueError, TypeError):
                        rsrp = -120  # Default to very weak signal
                    
                    # Extract SINR value
                    try:
                        sinr_str = signal_data.get("sinr", "0 dB")
                        if isinstance(sinr_str, str) and "dB" in sinr_str:
                            sinr_str = sinr_str.replace("dB", "").strip()
                        sinr = float(sinr_str)
                    except (ValueError, TypeError):
                        sinr = 0  # Default to neutral SINR
                    
                    # Calculate score (weighted average of normalized RSRP and SINR)
                    # RSRP typically ranges from -120 (poor) to -70 (excellent)
                    # SINR typically ranges from -10 (poor) to 20 (excellent)
                    rsrp_norm = max(0, min(100, (rsrp + 120) / 50 * 100))
                    sinr_norm = max(0, min(100, (sinr + 10) / 30 * 100))
                    score = 0.7 * rsrp_norm + 0.3 * sinr_norm
                    
                    # Store results
                    results[band] = {
                        "score": score,
                        "rsrp": rsrp,
                        "sinr": sinr
                    }
                    
                    self.log_message(f"Band {band}: RSRP={rsrp} dBm, SINR={sinr} dB, Score={score:.1f}", log_type="detailed")
                    
                    successful_tests += 1
                    self.log_message(f"✅ Tested {successful_tests}/{len(bands_to_test)} bands", log_type="standard")
                
                # Find top bands
                sorted_bands = sorted(results.items(), key=lambda x: x[1]["score"], reverse=True)
                top_bands = [band for band, data in sorted_bands if data["score"] > 0][:3]
                
                if not top_bands:
                    error_message = "⚠️ No usable bands found. Try again or check connection."
                    self.log_message(error_message, log_type="both")
                    self.master.after(0, lambda: messagebox.showwarning("Optimization Failed", error_message))
                    return
                
                # Generate report
                report_path = generate_report(results, optimisation_type="basic")
                
                # Show optimisation summary dialogue
                self.master.after(0, lambda: self.show_optimisation_summary(top_bands, results, report_path))
                
                # Play notification sound
                self.master.bell()
            except Exception as e:
                error_message = f"Optimisation error: {str(e)}"
                self.log_message(error_message, log_type="both")
                self.master.after(0, lambda: messagebox.showerror("Optimization Error", error_message))
                # Try to restore the original band configuration
                try:
                    # Use the original_band_config saved at the beginning of the method
                    if original_band_config:
                        self.log_message(f"Attempting to restore original bands: {', '.join(original_band_config)}", log_type="both")
                        apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, original_band_config)
                except Exception as restore_error:
                    restore_error_message = f"Failed to restore original band configuration: {str(restore_error)}"
                    self.log_message(restore_error_message, log_type="both")
                    self.master.after(0, lambda: messagebox.showerror("Restoration Error", restore_error_message))
            finally:
                # Re-enable optimization buttons
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
        if not hasattr(self, 'is_connected') or not self.is_connected:
            self.log_message("⚠️ Not connected. Cannot run enhanced optimisation.", log_type="both")
            return
        
        # Disable buttons to prevent multiple clicks
        if hasattr(self, 'optimise_button'):
            self.optimise_button.config(state=tk.DISABLED)
        if hasattr(self, 'enhanced_optimise_button'):
            self.enhanced_optimise_button.config(state=tk.DISABLED)
        if hasattr(self, 'speedtest_button'):
            self.speedtest_button.config(state=tk.DISABLED)
        
        # Save current band configuration before starting
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(band)
        
        self.log_message(f"Current band config saved: {', '.join(original_band_config) if original_band_config else 'No bands'}", log_type="detailed")
        
        # Run optimisation in a background thread
        threading.Thread(target=lambda: self.enhanced_optimise_thread(original_band_config), daemon=True).start()

    def enhanced_optimise_thread(self, original_band_config):
        try:
            # Test each band one by one
            results_4g = {}
            results_5g = {}
            
            # Initialize recommended results dictionary
            self.recommended_results = {
                '4G': {'bands': [], 'score': 0, 'metrics': {}},
                '5G': {'bands': [], 'score': 0, 'metrics': {}}
            }
            
            # Test each band one by one - use available bands
            self.log_message("🔄 Testing 4G bands...", log_type="both")
            for band in self.available_bands["4G"]:
                retry_count = 0
                max_retries = 2
                success = False
                
                while not success and retry_count <= max_retries:
                    try:
                        # Apply single band
                        self.log_message(f"Testing band {band}...", log_type="both")
                        apply_band_lock(
                            self.session or self.client,
                            self.router_ip.get(),
                            self.token,
                            [band]
                        )
                        success = True
                    except Exception as e:
                        error_str = str(e).lower()
                        # Check for session token errors
                        if ("wrong session token" in error_str or 
                            "125003" in error_str or 
                            "100003" in error_str or 
                            "needs login" in error_str or
                            "no rights" in error_str) and retry_count < max_retries:
                            # Session expired during band application, attempt reconnection
                            retry_count += 1
                            self.log_message(f"Session token error while applying band {band}. Reconnecting... (Attempt {retry_count})", log_type="both")
                            
                            # Reconnect using stored credentials
                            reconnect_success = self.silent_reconnect(
                                self.router_ip.get(),
                                self.username.get(),
                                self.password.get(),
                                self.use_api_lib.get()
                            )
                            
                            if reconnect_success:
                                self.log_message("Reconnected successfully, retrying band application", log_type="both")
                                time.sleep(2)  # Small delay before retry
                            else:
                                raise Exception(f"Failed to reconnect after session token error")
                        else:
                            # Other error, not retry-able
                            raise e
                
                    if not success:
                        self.log_message(f"Failed to apply band {band} after {max_retries} attempts, skipping", log_type="both")
                        continue
                    
                    # Wait for band to stabilize - increased to 10 seconds for better stability
                    time.sleep(10)
                    
                    # Get signal metrics - with retry for session errors
                    retry_count = 0
                    signal_data = None
                    
                    while signal_data is None and retry_count <= max_retries:
                        try:
                            signal_data = fetch_signal_data(
                                self,
                                self.session or self.client,
                                self.router_ip.get(),
                                self.token
                            )
                        except Exception as e:
                            error_str = str(e).lower()
                            if ("wrong session token" in error_str or 
                                "125003" in error_str or 
                                "100003" in error_str or 
                                "needs login" in error_str or
                                "no rights" in error_str) and retry_count < max_retries:
                                
                                retry_count += 1
                                self.log_message(f"Session token error while fetching signal data. Reconnecting... (Attempt {retry_count})", log_type="both")
                                
                                # Reconnect using stored credentials
                                reconnect_success = self.silent_reconnect(
                                    self.router_ip.get(),
                                    self.username.get(),
                                    self.password.get(),
                                    self.use_api_lib.get()
                                )
                                
                                if reconnect_success:
                                    self.log_message("Reconnected successfully, retrying signal data fetch", log_type="both")
                                    time.sleep(2)  # Small delay before retry
                                else:
                                    raise Exception(f"Failed to reconnect after session token error")
                            else:
                                raise e
                    
                    if not signal_data:
                        self.log_message(f"No signal data for band {band}, skipping", log_type="both")
                        continue
                    
                    # Run speedtest
                    speedtest_result = run_speedtest()
                    
                    # Extract signal metrics
                    rsrp_str = signal_data.get("rsrp", "-120 dBm")
                    if isinstance(rsrp_str, str) and "dBm" in rsrp_str:
                        rsrp_str = rsrp_str.replace("dBm", "").strip()
                    rsrp_float = float(rsrp_str)
                    
                    sinr_str = signal_data.get("sinr", "0 dB")
                    if isinstance(sinr_str, str) and "dB" in sinr_str:
                        sinr_str = sinr_str.replace("dB", "").strip()
                    sinr_float = float(sinr_str)
                    
                    # Store speed test results if successful
                    if speedtest_result["success"]:
                        download = speedtest_result["download"]
                        upload = speedtest_result["upload"]
                        ping = speedtest_result["ping"]
                    else:
                        download = 0
                        upload = 0
                        ping = 999
                    
                    # Calculate enhanced score with speed test results
                    # Calculate base score from RSRP and SINR
                    rsrp_norm = max(0, min(100, (rsrp_float + 140) / 96 * 100))
                    sinr_norm = max(0, min(100, (sinr_float + 20) / 50 * 100))
                    signal_score = 0.6 * rsrp_norm + 0.4 * sinr_norm
                    
                    # Calculate speed score (normalized to 100 Mbps)
                    download_norm = min(100, download / 1.0) if download > 0 else 0
                    upload_norm = min(100, upload / 1.0) if upload > 0 else 0
                    speed_score = 0.7 * download_norm + 0.3 * upload_norm
                    
                    # Combine signal and speed scores
                    # Enhanced algorithm: 40% signal quality, 60% speed
                    final_score = 0.4 * signal_score + 0.6 * speed_score
                    
                    # Store results
                    results_4g[band] = {
                        "score": final_score,
                        "rsrp": rsrp_float,
                        "sinr": sinr_float,
                        "download": download,
                        "upload": upload,
                        "ping": ping
                    }
                    
                    self.log_message(f"Band {band}: RSRP={rsrp_float} dBm, SINR={sinr_float} dB, Score={final_score:.1f}", log_type="detailed")
                    
            # Find best 4G band
            if results_4g:
                sorted_4g = sorted(results_4g.items(), key=lambda x: x[1]["score"], reverse=True)
                best_4g_band = sorted_4g[0][0] if sorted_4g else None
                
                if best_4g_band:
                    self.recommended_results['4G']['bands'] = [best_4g_band]
                    self.recommended_results['4G']['score'] = results_4g[best_4g_band]["score"]
                    self.recommended_results['4G']['metrics'] = {
                        "rsrp": results_4g[best_4g_band]["rsrp"],
                        "sinr": results_4g[best_4g_band]["sinr"],
                        "download": results_4g[best_4g_band]["download"],
                        "upload": results_4g[best_4g_band]["upload"],
                        "ping": results_4g[best_4g_band]["ping"]
                    }
            
            # Test 5G bands if available
            if self.available_bands["5G"]:
                self.log_message("🔄 Testing 5G bands...", log_type="both")
                for band in self.available_bands["5G"]:
                    retry_count = 0
                    max_retries = 2
                    success = False
                    
                    while not success and retry_count <= max_retries:
                        try:
                            # Apply single band
                            self.log_message(f"Testing band {band}...", log_type="both")
                            apply_band_lock(
                                self.session or self.client,
                                self.router_ip.get(),
                                self.token,
                                [band]
                            )
                            success = True
                        except Exception as e:
                            error_str = str(e).lower()
                            # Check for session token errors
                            if ("wrong session token" in error_str or 
                                "125003" in error_str or 
                                "100003" in error_str or 
                                "needs login" in error_str or
                                "no rights" in error_str) and retry_count < max_retries:
                                # Session expired during band application, attempt reconnection
                                retry_count += 1
                                self.log_message(f"Session token error while applying band {band}. Reconnecting... (Attempt {retry_count})", log_type="both")
                                
                                # Reconnect using stored credentials
                                reconnect_success = self.silent_reconnect(
                                    self.router_ip.get(),
                                    self.username.get(),
                                    self.password.get(),
                                    self.use_api_lib.get()
                                )
                                
                                if reconnect_success:
                                    self.log_message("Reconnected successfully, retrying band application", log_type="both")
                                    time.sleep(2)  # Small delay before retry
                                else:
                                    raise Exception(f"Failed to reconnect after session token error")
                            else:
                                # Other error, not retry-able
                                raise e
                    
                    if not success:
                        self.log_message(f"Failed to apply band {band} after {max_retries} attempts, skipping", log_type="both")
                        continue
                    
                    # Wait for band to stabilize
                    time.sleep(10)
                    
                    # Get signal metrics - with retry for session errors
                    retry_count = 0
                    signal_data = None
                    
                    while signal_data is None and retry_count <= max_retries:
                        try:
                            signal_data = fetch_signal_data(
                                self,
                                self.session or self.client,
                                self.router_ip.get(),
                                self.token
                            )
                        except Exception as e:
                            error_str = str(e).lower()
                            if ("wrong session token" in error_str or 
                                "125003" in error_str or 
                                "100003" in error_str or 
                                "needs login" in error_str or
                                "no rights" in error_str) and retry_count < max_retries:
                                
                                retry_count += 1
                                self.log_message(f"Session token error while fetching signal data. Reconnecting... (Attempt {retry_count})", log_type="both")
                                
                                # Reconnect using stored credentials
                                reconnect_success = self.silent_reconnect(
                                    self.router_ip.get(),
                                    self.username.get(),
                                    self.password.get(),
                                    self.use_api_lib.get()
                                )
                                
                                if reconnect_success:
                                    self.log_message("Reconnected successfully, retrying signal data fetch", log_type="both")
                                    time.sleep(2)  # Small delay before retry
                                else:
                                    raise Exception(f"Failed to reconnect after session token error")
                            else:
                                raise e
                    
                    if not signal_data:
                        self.log_message(f"No signal data for band {band}, skipping", log_type="both")
                        continue
                    
                    # Run speedtest
                    speedtest_result = run_speedtest()
                    
                    # Extract signal metrics
                    rsrp_str = signal_data.get("rsrp", "-120 dBm")
                    if isinstance(rsrp_str, str) and "dBm" in rsrp_str:
                        rsrp_str = rsrp_str.replace("dBm", "").strip()
                    rsrp_float = float(rsrp_str)
                    
                    sinr_str = signal_data.get("sinr", "0 dB")
                    if isinstance(sinr_str, str) and "dB" in sinr_str:
                        sinr_str = sinr_str.replace("dB", "").strip()
                    sinr_float = float(sinr_str)
                    
                    # Store speed test results if successful
                    if speedtest_result["success"]:
                        download = speedtest_result["download"]
                        upload = speedtest_result["upload"]
                        ping = speedtest_result["ping"]
                    else:
                        download = 0
                        upload = 0
                        ping = 999
                    
                    # Calculate enhanced score, similar to 4G logic
                    rsrp_norm = max(0, min(100, (rsrp_float + 140) / 96 * 100))
                    sinr_norm = max(0, min(100, (sinr_float + 20) / 50 * 100))
                    signal_score = 0.6 * rsrp_norm + 0.4 * sinr_norm
                    
                    # Calculate speed score (normalized to 100 Mbps)
                    download_norm = min(100, download / 1.0) if download > 0 else 0
                    upload_norm = min(100, upload / 1.0) if upload > 0 else 0
                    speed_score = 0.7 * download_norm + 0.3 * upload_norm
                    
                    # Combine signal and speed scores with different weights for 5G
                    # Enhanced algorithm for 5G: 30% signal quality, 70% speed
                    final_score = 0.3 * signal_score + 0.7 * speed_score
                    
                    # Store results
                    results_5g[band] = {
                        "score": final_score,
                        "rsrp": rsrp_float,
                        "sinr": sinr_float,
                        "download": download,
                        "upload": upload,
                        "ping": ping
                    }
                    
                    self.log_message(f"Band {band}: RSRP={rsrp_float} dBm, SINR={sinr_float} dB, Score={final_score:.1f}", log_type="detailed")
            
            # Find best 5G band
            if results_5g:
                sorted_5g = sorted(results_5g.items(), key=lambda x: x[1]["score"], reverse=True)
                best_5g_band = sorted_5g[0][0] if sorted_5g else None
                
                if best_5g_band:
                    self.recommended_results['5G']['bands'] = [best_5g_band]
                    self.recommended_results['5G']['score'] = results_5g[best_5g_band]["score"]
                    self.recommended_results['5G']['metrics'] = {
                        "rsrp": results_5g[best_5g_band]["rsrp"],
                        "sinr": results_5g[best_5g_band]["sinr"],
                        "download": results_5g[best_5g_band]["download"],
                        "upload": results_5g[best_5g_band]["upload"],
                        "ping": results_5g[best_5g_band]["ping"]
                    }
            
            # Generate report with both 4G and 5G results
            report_path = generate_report({
                '4G_results': results_4g,
                '5G_results': results_5g,
                'recommended': self.recommended_results
            }, optimisation_type="enhanced")
            
            # Restore original bands configuration with retry
            retry_count = 0
            max_retries = 2
            restore_success = False
            
            while not restore_success and retry_count <= max_retries:
                try:
                    self.log_message("Restoring original band configuration...", log_type="both")
                    apply_band_lock(
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token,
                        original_band_config
                    )
                    restore_success = True
                except Exception as e:
                    error_str = str(e).lower()
                    # Check for session token errors
                    if ("wrong session token" in error_str or 
                        "125003" in error_str or 
                        "100003" in error_str or 
                        "needs login" in error_str or
                        "no rights" in error_str) and retry_count < max_retries:
                        # Session expired during band restoration, attempt reconnection
                        retry_count += 1
                        self.log_message(f"Session token error while restoring band configuration. Reconnecting... (Attempt {retry_count})", log_type="both")
                        
                        # Reconnect using stored credentials
                        reconnect_success = self.silent_reconnect(
                            self.router_ip.get(),
                            self.username.get(),
                            self.password.get(),
                            self.use_api_lib.get()
                        )
                        
                        if reconnect_success:
                            self.log_message("Reconnected successfully, retrying band restoration", log_type="both")
                            time.sleep(2)  # Small delay before retry
                        else:
                            self.log_message("Failed to reconnect after session token error during band restoration", log_type="both")
                            break
                    else:
                        # Other error, not retry-able
                        self.log_message(f"Error restoring band configuration: {str(e)}", log_type="both")
                        break
            
            # Display report
            self.master.after(0, lambda: self.show_enhanced_optimisation_summary(
                results_4g, results_5g, self.recommended_results, report_path))
            
            # Play notification sound
            self.master.bell()
            
        except Exception as e:
            error_message = f"Enhanced optimisation error: {str(e)}"
            self.log_message(error_message, log_type="both")
            self.master.after(0, lambda: messagebox.showerror("Optimization Error", error_message))
            
            # Try to restore the original band configuration
            try:
                if original_band_config:
                    self.log_message(f"Attempting to restore original bands: {', '.join(original_band_config)}", log_type="both")
                    apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, original_band_config)
            except Exception as restore_error:
                restore_error_message = f"Failed to restore original bands: {str(restore_error)}"
                self.log_message(restore_error_message, log_type="both")
                self.master.after(0, lambda: messagebox.showerror("Restoration Error", restore_error_message))
            
        finally:
            # Re-enable optimization buttons
            if hasattr(self, 'optimise_button'):
                self.master.after(0, lambda: self.optimise_button.config(state=tk.NORMAL))
            if hasattr(self, 'enhanced_optimise_button'):
                self.master.after(0, lambda: self.enhanced_optimise_button.config(state=tk.NORMAL))
            if hasattr(self, 'speedtest_button'):
                self.master.after(0, lambda: self.speedtest_button.config(state=tk.NORMAL))

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
            "auto_connect": self.auto_connect.get(),
            "use_api_lib": self.use_api_lib.get(),
            "run_speed_on_start": self.run_speed_on_start.get(),
            "notify_on_signal_change": self.notify_on_signal_change.get(),
            "selected_bands": [band for band, var in self.band_vars.items() if var.get()]
        }
        
        # Save to file
        try:
            with open("config.json", "w") as f:
                json.dump(config, f, indent=4, sort_keys=True)
            self.log_message("Configuration saved", log_type="detailed")
        except Exception as e:
            self.log_message(f"Failed to save configuration: {str(e)}", log_type="detailed")
            
    def show_donation_dialog(self):
        """Show a dialog with donation information"""
        try:
            donation_text = "If you find this tool helpful, please consider supporting its development.\n\n"
            donation_text += "PayPal: donate@example.com\n"
            donation_text += "BTC: bc1qxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"
            donation_text += "ETH: 0xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n\n"
            donation_text += "Thank you for your support!"
            
            # Create a custom dialog
            dialog = tk.Toplevel(self.master)
            dialog.title("Support Development")
            dialog.geometry("400x300")
            dialog.resizable(False, False)
            dialog.transient(self.master)
            dialog.grab_set()
            
            # Add content
            ttk.Label(dialog, text="Support Development", font=("", 12, "bold")).pack(pady=10)
            
            message = ttk.Label(dialog, text=donation_text, wraplength=380, justify=tk.CENTER)
            message.pack(padx=20, pady=10, fill=tk.BOTH, expand=True)
            
            # Add close button
            close_button = ttk.Button(dialog, text="Close", command=dialog.destroy)
            close_button.pack(pady=10)
            
            # Center the dialog on the parent window
            dialog.update_idletasks()
            x = self.master.winfo_x() + (self.master.winfo_width() - dialog.winfo_width()) // 2
            y = self.master.winfo_y() + (self.master.winfo_height() - dialog.winfo_height()) // 2
            dialog.geometry(f"+{max(0, x)}+{max(0, y)}")
            
        except Exception as e:
            self.log_message(f"Error showing donation dialog: {str(e)}", log_type="both")

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
            # Stop any auto-refresh and cancel polling task
            if hasattr(self, 'auto_refresh') and self.auto_refresh.get():
                self.toggle_auto_refresh()
                
            # Explicitly cancel polling task if it exists
            if hasattr(self, 'poll_status_task') and self.poll_status_task:
                try:
                    self.master.after_cancel(self.poll_status_task)
                    self.poll_status_task = None
                    self.log_message("Cancelled polling task", log_type="detailed")
                except Exception as e:
                    self.log_message(f"Error cancelling poll task: {str(e)}", log_type="detailed")
                
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

    def refresh_thread(self):
        """Background thread for refreshing signal data"""
        try:
            # Check if we need to reconnect
            if not hasattr(self, 'client') or self.client is None:
                self.log_message("Client is None, attempting silent reconnect", log_type="detailed")
                silent_reconnect_success = self.silent_reconnect(
                    self.router_ip.get(), 
                    self.username.get(), 
                    self.password.get(), 
                    getattr(self, 'use_api_value', True))
                
                if not silent_reconnect_success:
                    self.log_message("Silent reconnect failed, cannot refresh signal", log_type="both")
                    self.update_signal_ui({'rsrp': '--', 'rsrq': '--', 'sinr': '--', 'band': '--'})
                    self.refresh_in_progress = False
                    return
            
            # Log session info before attempting to fetch data
            self.log_message("Attempting to fetch signal data with current session", log_type="detailed")
            
            # Fetch signal data using the standalone function
            signal_data = fetch_signal_data(self, self.client, self.router_ip.get(), getattr(self, 'token', None))
            
            # If we got an empty result or session timeout was detected, try to reconnect
            if not signal_data or hasattr(self, 'session_timeout_detected') and self.session_timeout_detected:
                self.log_message("Session timeout detected or empty signal data, attempting to reconnect", log_type="detailed")
                # Reset the flag
                if hasattr(self, 'session_timeout_detected'):
                    self.session_timeout_detected = False
                
                # Try to reconnect
                silent_reconnect_success = self.silent_reconnect(
                    self.router_ip.get(), 
                    self.username.get(), 
                    self.password.get(), 
                    getattr(self, 'use_api_value', True))
                
                if silent_reconnect_success:
                    # Try again with the new connection
                    signal_data = fetch_signal_data(self, self.client, self.router_ip.get(), getattr(self, 'token', None))
            
            # Update UI with the fetched data
            if signal_data:
                # Schedule UI update on the main thread
                self.master.after(0, lambda: self.update_signal_ui(signal_data))
            else:
                self.master.after(0, lambda: self.update_signal_ui({'rsrp': '--', 'rsrq': '--', 'sinr': '--', 'band': '--'}))
                
        except Exception as e:
            self.log_message(f"Error in refresh thread: {str(e)}", log_type="both")
            self.master.after(0, lambda: self.update_signal_ui({'rsrp': '--', 'rsrq': '--', 'sinr': '--', 'band': '--'}))
        finally:
            # Reset the flag when done
            self.refresh_in_progress = False

    def update_signal_ui(self, signal_data):
        """Update UI with signal data"""
        # Define mapping between signal_data keys and display keys
        key_mapping = {
            'rsrp': 'RSRP',
            'rsrq': 'RSRQ',
            'sinr': 'SINR',
            'band': 'BAND',
            'primary_band': 'PRIMARY_BAND',
            'mode': 'NETWORK_TYPE',
            'plmn_name': 'CARRIER',
            # Removing download/upload from auto-updating - these will only be updated by speed tests
            # 'download': 'DOWNLOAD',
            # 'upload': 'UPLOAD'
        }
        
        # Debug log received signal data
        self.log_message(f"Raw signal data received: {signal_data}", log_type="detailed")
        
        # Process each key
        for data_key, ui_key in key_mapping.items():
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
                # Special handling for band to show all bands when available
                elif data_key == 'band' and ui_key == 'BAND':
                    # Use primary band or current band
                    display_value = signal_data[data_key]
                    
                    # Handle empty or null values
                    if display_value is None or display_value == '' or display_value == '--':
                        display_value = 'N/A'
                    
                    # If we have the 'bands' field with multiple bands, use it instead
                    if 'bands' in signal_data and signal_data['bands'] and signal_data['bands'] != '--':
                        # Display all bands instead of just the primary one
                        display_value = signal_data['bands']
                    
                    self.signal_info[ui_key].set(display_value)
                    
                    # For band, ensure we check all active bands in the UI
                    if display_value != 'N/A' and display_value != '--':
                        # If we have multiple bands, check them all in the UI
                        if 'bands' in signal_data and signal_data['bands']:
                            # Use all bands for the checkboxes
                            self.select_active_band(signal_data['bands'])
                        else:
                            # Otherwise just use the primary band
                            primary_band = signal_data.get('primary_band', signal_data['band']) 
                            self.select_active_band(primary_band)
                # Special handling for primary band display
                elif data_key == 'primary_band' and ui_key == 'PRIMARY_BAND':
                    display_value = signal_data[data_key]
                    
                    # Handle empty or null values
                    if display_value is None or display_value == '' or display_value == '--':
                        # Fall back to the regular band field if primary is not set
                        display_value = signal_data.get('band', 'N/A')
                        if display_value is None or display_value == '' or display_value == '--':
                            display_value = 'N/A'
                    
                    self.signal_info[ui_key].set(display_value)
                else:
                    # Use data as is
                    display_value = signal_data[data_key]
                    
                    # Handle empty or null values
                    if display_value is None or display_value == '' or display_value == '--':
                        display_value = 'N/A'
                    
                    self.signal_info[ui_key].set(display_value)
            # Special case for PRIMARY_BAND if not in the data
            elif ui_key == 'PRIMARY_BAND' and 'band' in signal_data and 'primary_band' not in signal_data:
                # Use band as fallback for primary_band
                display_value = signal_data['band']
                if display_value is None or display_value == '' or display_value == '--':
                    display_value = 'N/A'
                self.signal_info[ui_key].set(display_value)

        # Update RSRP color
        if 'rsrp' in signal_data and signal_data['rsrp'] != '--':
            try:
                rsrp_value = float(signal_data['rsrp'].replace("dBm", "").strip())
                self.update_rsrp_color(rsrp_value)
            except (ValueError, TypeError) as e:
                self.log_message(f"Could not parse RSRP value: {signal_data['rsrp']} - {str(e)}", log_type="detailed")
                
        # Check for significant signal changes
        self.check_signal_changes(signal_data)

    def update_rsrp_color(self, rsrp_value):
        """Update the color of the RSRP value based on signal strength"""
        try:
            # Define color ranges for RSRP
            if rsrp_value >= -80:  # Excellent
                color = "#00A000"  # Green
            elif rsrp_value >= -90:  # Good
                color = "#A0A000"  # Yellow-green
            elif rsrp_value >= -100:  # Fair
                color = "#A05000"  # Orange
            else:  # Poor
                color = "#A00000"  # Red
                
            # Find the RSRP label and update its color
            for widget in self.master.winfo_children():
                if isinstance(widget, tk.Frame):
                    for inner_widget in widget.winfo_children():
                        if isinstance(inner_widget, ttk.LabelFrame) and inner_widget.winfo_children():
                            for label_widget in inner_widget.winfo_children():
                                if hasattr(label_widget, 'cget') and label_widget.cget('textvariable') == self.signal_info['RSRP']:
                                    label_widget.config(foreground=color)
                                    return
        except Exception as e:
            self.log_message(f"Error updating RSRP color: {str(e)}", log_type="detailed")

    def select_active_band(self, active_band):
        """Helper method to automatically select the active band in the UI"""
        if not hasattr(self, 'band_vars') or not self.band_vars:
            return
        
        # Parse active band string (might be a single band or comma-separated list)
        active_bands = []
        if isinstance(active_band, str):
            # Check if it's a comma-separated list of bands
            if ',' in active_band:
                # Split the string into individual bands
                active_bands = [band.strip() for band in active_band.split(',')]
                self.log_message(f"Selecting multiple active bands: {active_bands}", log_type="detailed")
            else:
                # Single band
                active_bands = [active_band.strip()]
                self.log_message(f"Selecting single active band: {active_band}", log_type="detailed")
        else:
            # Not a valid band string
            self.log_message(f"Invalid active band format: {active_band}", log_type="detailed")
            return
        
        # First, uncheck all band checkboxes
        self.uncheck_all_bands()
        
        # Process each band and try to check the corresponding checkbox
        for band in active_bands:
            # First check if this is a 5G band (starts with 'n')
            is_5g = isinstance(band, str) and band.lower().startswith('n')
            
            # Clean the band value
            clean_band = band
            if isinstance(band, str):
                # For 4G bands, ensure we have a 'B' prefix
                if not is_5g and not band.upper().startswith('B') and band.replace('B', '').isdigit():
                    clean_band = f"B{band.replace('B', '')}"
                
                # For 5G bands, ensure we have an 'n' prefix
                if is_5g and not band.lower().startswith('n'):
                    clean_band = f"n{band.replace('n', '')}"
            
            self.log_message(f"Checking for band: {clean_band}", log_type="detailed")
            
            # Try various formats to find the band checkbox
            bands_to_try = [
                clean_band,                # e.g., "B7" or "n78"
                clean_band.upper(),        # e.g., "B7" or "N78"
                clean_band.lower(),        # e.g., "b7" or "n78"
                clean_band.replace('B', '').replace('b', '').replace('N', '').replace('n', '')  # e.g., "7" or "78"
            ]
            
            # Try to match the band in the checkboxes
            found = False
            for band_to_try in bands_to_try:
                if band_to_try in self.band_vars:
                    # Set the checkbox to checked
                    self.band_vars[band_to_try].set(True)
                    self.log_message(f"Selected active band: {band_to_try}", log_type="detailed")
                    found = True
                    break
            
            if not found:
                self.log_message(f"Could not find checkbox for band: {band} (not in available bands)", log_type="detailed")
        
        # Log available bands for debugging if we couldn't find any matches
        if not any(self.band_vars[band].get() for band in self.band_vars):
            available_bands = list(self.band_vars.keys())
            if available_bands:
                self.log_message(f"Available band checkboxes: {available_bands}", log_type="detailed")

    def uncheck_all_bands(self):
        """Uncheck all band checkboxes"""
        if not hasattr(self, 'band_vars') or not self.band_vars:
            return
        
        # Uncheck all band checkboxes
        for band_var_key in self.band_vars:
            self.band_vars[band_var_key].set(False)

    def check_signal_changes(self, signal_data):
        """Monitor significant changes in signal metrics and notify the user"""
        if not self.notify_on_signal_change.get() or not signal_data:
            return
            
        changes = []
        
        # Only check for band changes as requested by user, not RSRQ or other signal metrics
        
        # Check for primary band changes
        if 'band' in signal_data and 'band' in self.last_signal:
            if signal_data['band'] != self.last_signal['band']:
                changes.append(f"Band: {self.last_signal['band']} → {signal_data['band']}")
        
        # Check for changes in the full bands list
        if 'bands' in signal_data and 'bands' in self.last_signal:
            if signal_data['bands'] != self.last_signal['bands']:
                changes.append(f"All Bands: {self.last_signal['bands']} → {signal_data['bands']}")
        
        # Check for changes in primary band specifically 
        if 'primary_band' in signal_data and 'primary_band' in self.last_signal:
            if signal_data['primary_band'] != self.last_signal['primary_band']:
                changes.append(f"Primary Band: {self.last_signal['primary_band']} → {signal_data['primary_band']}")
                
        # Notify if there are band changes
        if changes:
            message = " | ".join(changes)
            self.log_message(f"Band change detected: {message}", log_type="both")
            
            # Show system notification if available
            if NOTIFICATIONS_AVAILABLE:
                try:
                    notifier = ToastNotifier()
                    notifier.show_toast(
                        "Band Change Detected",
                        message,
                        duration=5,
                        threaded=True
                    )
                except Exception as e:
                    self.log_message(f"Error showing notification: {str(e)}", log_type="detailed")
                    
        # Update last signal data
        self.last_signal = signal_data.copy()

    def check_library_version(self):
        """Check if the Huawei LTE API library is available and warn if not"""
        if not HUAWEI_API_AVAILABLE and not self.api_restriction_warning_shown:
            messagebox.showwarning(
                "API Library Not Found", 
                "The Huawei LTE API library is not installed. Some features may be limited.\n\n"
                "To install the library, run: pip install huawei-lte-api"
            )
            self.api_restriction_warning_shown = True
            # Disable API option
            self.use_api_lib.set(False)
        
        # Alternatively, remove the API library check by editing __init__ to not call this method

    def store_credentials(self, router_ip, username, password, use_api):
        """Store credentials for reconnection purposes"""
        self.stored_ip = router_ip
        self.stored_username = username
        self.stored_password = password
        self.stored_api_mode = use_api
        self.log_message("Stored credentials for auto-reconnection", log_type="detailed")

    def connect_to_router(self):
        """Connect to the Huawei router and get signal data"""
        try:
            # Get connection details
            router_ip = self.router_ip.get()
            username = self.username.get()
            password = self.password.get()
            use_api = self.connection_mode.get() == "API"
            
            if not router_ip:
                messagebox.showerror("Connection Error", "Please enter router IP address")
                return
                
            if not username or not password:
                messagebox.showerror("Connection Error", "Please enter username and password")
                return
                
            # Store credentials for reconnection
            self.store_credentials(router_ip, username, password, use_api)
            
            # Show connecting status
            self.status_var.set("Connecting...")
            self.log_message(f"Connecting to {router_ip} using {'API' if use_api else 'Web'} mode...", log_type="both")
            
            # Attempt login
            login_result = login_to_router(router_ip, username, password, use_api)
            
            if not login_result or not login_result[0]:
                error_msg = login_result[2] if login_result and len(login_result) > 2 else "Unknown error"
                self.status_var.set(f"Connection failed: {error_msg}")
                self.log_message(f"Connection failed: {error_msg}", log_type="both")
                messagebox.showerror("Connection Error", f"Failed to connect to router: {error_msg}")
                return
                
            # Process login result
            if use_api:
                self.client = login_result[0]  # huawei_lte_api.Client instance
                self.session = None
                self.token = None
                self.connection_type = "API"
            else:
                self.client = None
                self.session = login_result[0]  # requests.Session
                self.token = login_result[1]    # SessionID token
                self.connection_type = "Web"
                
            self.is_connected = True
            self.status_var.set(f"Connected to {router_ip} via {self.connection_type}")
            self.log_message(f"Successfully connected to {router_ip} via {self.connection_type}", log_type="both")
            
            # Initialize or reset connection-related variables
            self.reconnection_attempts = 0
            self.last_session_activity = time.time()
            self.session_timeout_detected = False
            
            # Start data polling
            self.start_polling()
            
            # Start keepalive mechanism
            self.start_session_keepalive()
            
            # Update UI elements
            self.connect_button.config(text="Disconnect")
            self.router_ip_entry.config(state="disabled")
            self.username_entry.config(state="disabled")
            self.password_entry.config(state="disabled")
            self.conn_mode_dropdown.config(state="disabled")
            
            # Get available bands after successful connection
            self.fetch_supported_bands()
            
        except Exception as e:
            self.status_var.set(f"Connection error: {str(e)}")
            self.log_message(f"Connection error: {str(e)}", log_type="both")
            messagebox.showerror("Connection Error", f"Error connecting to router: {str(e)}")
            self.is_connected = False

    def auto_reconnect(self):
        """Automatically reconnect using stored credentials"""
        if not hasattr(self, 'stored_ip') or not self.stored_ip:
            self.log_message("No stored credentials for auto-reconnection", log_type="both")
            return False
            
        self.log_message("Auto-reconnecting with stored credentials...", log_type="both")
        try:
            return self.silent_reconnect(
                self.stored_ip,
                self.stored_username,
                self.stored_password,
                self.stored_api_mode
            )
        except Exception as e:
            self.log_message(f"Auto-reconnect failed: {str(e)}", log_type="both")
            return False

    def poll_status(self):
        """Poll signal status at regular intervals"""
        try:
            # Check if we should still be polling
            if not self.is_connected:
                self.log_message("Polling stopped - disconnected", log_type="detailed")
                self.poll_status_task = None
                return
                
            if not self.auto_refresh.get():
                self.log_message("Polling stopped - auto-refresh disabled", log_type="detailed")
                self.poll_status_task = None
                return
            
            # Add failure counter logic to prevent infinite retries
            if not hasattr(self, 'poll_failure_count'):
                self.poll_failure_count = 0
                
            # Check if session timeout was detected
            if hasattr(self, 'session_timeout_detected') and self.session_timeout_detected:
                self.log_message("Session timeout detected. Attempting auto-reconnect...", log_type="both")
                reconnect_result = self.auto_reconnect()
                if reconnect_result:
                    self.session_timeout_detected = False
                    self.poll_failure_count = 0
                    self.log_message("Auto-reconnect successful", log_type="both")
                else:
                    self.log_message("Auto-reconnect failed", log_type="both")
                    self.poll_failure_count += 1
            
            # Limit consecutive failures
            if hasattr(self, 'poll_failure_count') and self.poll_failure_count >= 5:
                error_message = "Auto-refresh disabled after 5 consecutive failures. The router may be unresponsive."
                self.log_message(error_message, log_type="both")
                self.auto_refresh.set(False)
                
                # Update error display in UI
                self.master.after(0, lambda: self.error_display.config(text=error_message))
                
                # Show a notification
                try:
                    if NOTIFICATIONS_AVAILABLE:
                        toaster = ToastNotifier()
                        toaster.show_toast(
                            "Auto-refresh Disabled",
                            error_message,
                            icon_path=None,
                            duration=5,
                            threaded=True
                        )
                except Exception:
                    pass
                
                self.poll_status_task = None
                return
            
            # Refresh signal data
            try:
                self.refresh_signal()
                self.log_message("Auto-refreshed signal data", log_type="detailed")
                # Reset failure counter on success
                self.poll_failure_count = 0
                # Also reset session timeout flag
                if hasattr(self, 'session_timeout_detected'):
                    self.session_timeout_detected = False
            except Exception as e:
                error_str = str(e)
                # Check if this is a session timeout error
                if "No rights" in error_str or "needs login" in error_str or "100003" in error_str or "login required" in error_str:
                    self.log_message("Session timeout detected in polling, will attempt reconnect", log_type="detailed")
                    self.session_timeout_detected = True
                
                # Increment failure counter
                self.poll_failure_count += 1
                self.log_message(f"Error in auto-refresh ({self.poll_failure_count}/5): {str(e)}", log_type="both")
            
        except Exception as e:
            self.log_message(f"Error in polling task: {str(e)}", log_type="both")
        finally:
            # Always schedule the next refresh, regardless of current state
            # This ensures continuous polling as long as auto-refresh is enabled
            if self.is_connected and self.auto_refresh.get():
                try:
                    # Use a shorter interval if we're waiting for reconnection
                    interval = 5000 if hasattr(self, 'session_timeout_detected') and self.session_timeout_detected else self.signal_update_interval
                    self.poll_status_task = self.master.after(interval, self.poll_status)
                    self.log_message(f"Scheduled next poll in {interval/1000} seconds", log_type="detailed")
                except Exception as e:
                    self.log_message(f"Error scheduling next poll: {str(e)}", log_type="detailed")
            else:
                self.poll_status_task = None

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