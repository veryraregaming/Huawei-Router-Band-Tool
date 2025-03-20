import tkinter as tk
from tkinter import messagebox, ttk, Checkbutton, IntVar, filedialog
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
    """Fetch signal data using the huawei-lte-api library"""
    signal_data = {}
    
    try:
        # Get device signal information
        try:
            device_signal = client.device.signal()
            self.log_message(f"Device signal data: {device_signal}", log_type="detailed")
            
            # Map signal metrics from the API response
            if 'rsrp' in device_signal:
                signal_data['RSRP'] = device_signal['rsrp']
            if 'rsrq' in device_signal:
                signal_data['RSRQ'] = device_signal['rsrq']
            if 'rssi' in device_signal:
                signal_data['RSSI'] = device_signal['rssi']
            if 'sinr' in device_signal:
                signal_data['SINR'] = device_signal['sinr']
                
            # Handle 5G metrics
            if 'ltenrrsrp' in device_signal:
                signal_data['NRRSRP'] = device_signal['ltenrrsrp']
            if 'ltenrrsrq' in device_signal:
                signal_data['NRRSRQ'] = device_signal['ltenrrsrq']
            if 'ltenrsinr' in device_signal:
                signal_data['NRSINR'] = device_signal['ltenrsinr']
        except Exception as e:
            self.log_message(f"Error fetching device signal: {str(e)}", log_type="both")
            
        # Get network information
        try:
            net_mode_info = client.net.net_mode()
            self.log_message(f"Network mode: {net_mode_info}", log_type="detailed")
            
            # Extract band information
            if 'LTEBand' in net_mode_info:
                lte_band_hex = net_mode_info['LTEBand']
                try:
                    # Convert hex to band numbers
                    band_hex = int(lte_band_hex, 16)
                    active_bands = []
                    for band_num, band_mask in BAND_MAP.items():
                        if band_hex & band_mask:
                            active_bands.append(f"B{band_num}")
                    if active_bands:
                        signal_data["BAND"] = ", ".join(active_bands)
                except ValueError:
                    signal_data["BAND"] = lte_band_hex
        except Exception as e:
            self.log_message(f"Error fetching network mode: {str(e)}", log_type="both")
            
        # Get current PLMN (carrier) information
        try:
            plmn_info = client.net.current_plmn()
            self.log_message(f"PLMN info: {plmn_info}", log_type="detailed")
            
            if 'FullName' in plmn_info:
                signal_data['CARRIER'] = plmn_info['FullName']
                
            # Get network type
            if 'Rat' in plmn_info:
                rat_value = plmn_info['Rat']
                rat_types = {"0": "No Service", "1": "GSM", "2": "GPRS", 
                           "3": "EDGE", "4": "WCDMA", "5": "HSDPA", 
                           "6": "HSUPA", "7": "LTE", "8": "CDMA", 
                           "9": "EVDO", "10": "HSPA+", "19": "LTE+", 
                           "20": "5G NSA", "21": "5G SA"}
                signal_data["NETWORK_TYPE"] = rat_types.get(rat_value, f"Unknown ({rat_value})")
        except Exception as e:
            self.log_message(f"Error fetching PLMN info: {str(e)}", log_type="both")
            
        # Get traffic statistics
        try:
            traffic_stats = client.monitoring.traffic_statistics()
            self.log_message(f"Traffic stats: {traffic_stats}", log_type="detailed")
            
            if 'CurrentDownloadRate' in traffic_stats:
                try:
                    dl_mbps = float(traffic_stats['CurrentDownloadRate']) / 1024 / 1024
                    signal_data["DOWNLOAD"] = f"{dl_mbps:.2f} Mbps"
                except ValueError:
                    pass
                
            if 'CurrentUploadRate' in traffic_stats:
                try:
                    ul_mbps = float(traffic_stats['CurrentUploadRate']) / 1024 / 1024
                    signal_data["UPLOAD"] = f"{ul_mbps:.2f} Mbps"
                except ValueError:
                    pass
        except Exception as e:
            self.log_message(f"Error fetching traffic stats: {str(e)}", log_type="both")
            
        # Get status information
        try:
            status_info = client.monitoring.status()
            self.log_message(f"Status info: {status_info}", log_type="detailed")
            
            if 'ConnectionStatus' in status_info:
                signal_data['CONNECTION_STATUS'] = status_info['ConnectionStatus']
                
        except Exception as e:
            self.log_message(f"Error fetching status: {str(e)}", log_type="both")
            
    except Exception as e:
        self.log_message(f"Error in API-based signal fetch: {str(e)}", log_type="both")
    
    if signal_data:
        self.log_message(f"API - Parsed signal data: {signal_data}", log_type="detailed")
        return signal_data
    else:
        self.log_message("Failed to fetch signal data via API", log_type="both")
        return None

# Unified fetch_signal_data function
def fetch_signal_data(self, session, ip, token):
    # Check if we're using huawei-lte-api client
    if HUAWEI_API_AVAILABLE and isinstance(session, Client):
        try:
            # Using API Library
            signal_data = fetch_signal_data_api(self, session, ip)
            
            # Log verbose data only to the detailed log
            if hasattr(self, 'log_message'):
                for key, value in signal_data.items():
                    if key not in ["RSRP", "RSRQ", "SINR", "BAND", "CARRIER", "NETWORK_TYPE", "DOWNLOAD", "UPLOAD", "CONNECTION_STATUS"]:
                        self.log_message(f"{key}: {value}", log_type="detailed")
                        
            return signal_data
        except Exception as e:
            if hasattr(self, 'log_message'):
                self.log_message(f"API error fetching signal data: {str(e)}", log_type="both")
            return None
    
    # Legacy implementation for regular requests.Session
    signal_data = {}
    
    # Try enhanced API access methods based on successful implementations
    try:
        # First get a fresh token - important for API stability
        token_response = session.get(f"http://{ip}{TOKEN_ENDPOINT}", timeout=10)
        if token_response.status_code == 200:
            token_data = ET.fromstring(token_response.text)
            fresh_token = token_data.find("TokInfo").text
            session_id = token_data.find("SesInfo").text if token_data.find("SesInfo") is not None else None
            
            headers = {
                "__RequestVerificationToken": fresh_token,
                "Content-Type": "application/xml",
                "Accept": "application/xml",
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                "Referer": f"http://{ip}/html/home.html"
            }
            
            if session_id:
                headers["Cookie"] = f"SessionID={session_id}"
            
            # Try multiple methods to enable signal monitoring
            monitoring_payloads = [
                "<request><Enable>1</Enable></request>",
                "<request><EnableSignalMonitoring>1</EnableSignalMonitoring></request>",
                "<request><SignalMonitoring>1</SignalMonitoring></request>",
                "<request><EnableDetailedMetrics>1</EnableDetailedMetrics></request>"
            ]
            
            for payload in monitoring_payloads:
                try:
                    session.post(f"http://{ip}{SET_MONITORING_ENDPOINT}", 
                                 data=payload, 
                                 headers=headers, 
                                 timeout=5)
                except:
                    pass
    except:
        # Continue even if this part fails
        pass
        
    # First try regular endpoints
    for endpoint in SIGNAL_ENDPOINTS:
        try:
            url = f"http://{ip}{endpoint}"
            self.log_message(f"Attempting to fetch signal data from {url}", log_type="detailed")
            headers = {
                "__RequestVerificationToken": token,
                "Content-Type": "application/xml",
                "Accept": "application/xml",
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                "Referer": f"http://{ip}/html/home.html"
            }
            response = session.get(url, headers=headers, timeout=10)
            
            if response.status_code == 200:
                try:
                    # Print raw XML for debugging valuable endpoints
                    if endpoint in ["/api/device/signal", "/api/net/signal"]:
                        self.log_message(f"Response: {response.text[:200]}...", log_type="detailed")
                    
                    data = ET.fromstring(response.text)
                    # Check if we got an error response
                    error_code = data.find("error/code")
                    if error_code is not None:
                        error_code_text = error_code.text
                        if error_code_text in ["100003", "125002"]:
                            if endpoint == "/api/monitoring/status":
                                self.log_message(f"Router has API restrictions (Error {error_code_text})", log_type="detailed")
                                if not self.api_restriction_warning_shown:
                                    messagebox.showwarning("API Restriction", 
                                        "Your router has API restrictions that prevent accessing signal data.\n"
                                        "This is common with carrier-locked devices and limits functionality.\n"
                                        "Limited functionality will be available.")
                                    self.api_restriction_warning_shown = True
                        continue
                    
                    # Extract data from working endpoints
                    if endpoint == "/api/net/current-plmn":
                        rat = data.find("Rat")
                        if rat is not None:
                            rat_value = rat.text
                            rat_types = {"0": "No Service", "1": "GSM", "2": "GPRS", 
                                        "3": "EDGE", "4": "WCDMA", "5": "HSDPA", 
                                        "6": "HSUPA", "7": "LTE", "8": "CDMA", 
                                        "9": "EVDO", "10": "HSPA+", "19": "LTE+", 
                                        "20": "5G NSA", "21": "5G SA"}
                            signal_data["NETWORK_TYPE"] = rat_types.get(rat_value, f"Unknown ({rat_value})")
                        
                        spn = data.find("FullName")
                        if spn is not None:
                            signal_data["CARRIER"] = spn.text
                    
                    elif endpoint == "/api/monitoring/traffic-statistics":
                        # Extract connection speed information
                        dl_rate = data.find("CurrentDownloadRate")
                        ul_rate = data.find("CurrentUploadRate")
                        if dl_rate is not None:
                            try:
                                dl_mbps = float(dl_rate.text) / 1024 / 1024
                                signal_data["DOWNLOAD"] = f"{dl_mbps:.2f} Mbps"
                            except ValueError:
                                pass
                        if ul_rate is not None:
                            try:
                                ul_mbps = float(ul_rate.text) / 1024 / 1024
                                signal_data["UPLOAD"] = f"{ul_mbps:.2f} Mbps"
                            except ValueError:
                                pass
                    
                    elif endpoint == "/api/device/signal":
                        # Special handling for device signal endpoint which may contain full signal metrics
                        for field in ["rsrp", "rsrq", "rssi", "sinr", "rscp", "ecio", "ltenrrsrp", "ltenrrsrq", "ltenrsinr"]:
                            element = data.find(field)
                            if element is not None:
                                field_upper = field.upper()
                                if field.startswith("ltenr"):
                                    # Format 5G fields
                                    field_upper = "NR" + field_upper[5:]
                                signal_data[field_upper] = element.text
                    
                    elif endpoint == "/api/net/signal":
                        # Some models use this endpoint for signal data
                        for field in ["cell_id", "pci", "ecgi", "earfcn", "rsrp", "rsrq", "rssi", "sinr", "band"]:
                            element = data.find(field)
                            if element is not None:
                                signal_data[field.upper()] = element.text
                    
                    # Standard signal data extraction for fields that might be available
                    for field in ["rsrp", "rsrq", "sinr", "rssi", "band", "nrrsrp", "nrrsrq", "nrsinr",
                                "cell_id", "mode", "frequency", "SignalRsrp", "SignalRsrq", "SignalSinr",
                                "ConnectionStatus", "CurrentNetworkType"]:
                        element = data.find(field)
                        if element is not None:
                            signal_data[field.upper()] = element.text
                            
                except ET.ParseError as e:
                    self.log_message(f"Failed to parse XML from {endpoint}: {str(e)}")
                    continue
        except Exception as e:
            self.log_message(f"Request failed for {endpoint}: {str(e)}")
            continue
    
    # Check for band information from the router settings
    if "BAND" not in signal_data:
        try:
            band_response = session.get(f"http://{ip}{NET_MODE_ENDPOINT}", headers=headers, timeout=10)
            if band_response.status_code == 200:
                band_data = ET.fromstring(band_response.text)
                lte_band = band_data.find("LTEBand")
                if lte_band is not None:
                    # Convert hex to band numbers
                    try:
                        band_hex = int(lte_band.text, 16)
                        active_bands = []
                        for band_num, band_mask in BAND_MAP.items():
                            if band_hex & band_mask:
                                active_bands.append(f"B{band_num}")
                        if active_bands:
                            signal_data["BAND"] = ", ".join(active_bands)
                    except ValueError:
                        pass
        except:
            pass
    
    if signal_data:
        self.log_message(f"Parsed signal data: {signal_data}")
        return signal_data
    
    # If we're here, we couldn't get any signal data, provide fallback info
    if session:
        self.log_message("Limited data due to router API restrictions.")
        return {"NETWORK_TYPE": "LTE", "RSRP": "--", "RSRQ": "--", "SINR": "--", "BAND": "--"}
    
    self.log_message("Failed to fetch signal data from all endpoints.")
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

class BandOptimiserApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Huawei Band Optimiser")
        
        # Configure root window
        self.root.geometry("850x650")
        self.root.minsize(800, 600)
        
        # Configuration variables
        self.config = load_config()
        self.router_ip = tk.StringVar(value=self.config.get("router_ip", ""))
        self.username = tk.StringVar(value=self.config.get("username", ""))
        self.password = tk.StringVar(value=self.config.get("password", ""))
        
        # Router connection settings
        self.auto_connect = tk.BooleanVar(value=self.config.get("auto_connect", False))
        self.use_api_lib = tk.BooleanVar(value=self.config.get("use_api_lib", True))
        self.speedtest_on_startup = tk.BooleanVar(value=self.config.get("speedtest_on_startup", False))
        
        # Set up traces for config changes
        self.auto_connect.trace_add("write", self.save_config_callback)
        self.use_api_lib.trace_add("write", self.save_config_callback)
        self.speedtest_on_startup.trace_add("write", self.save_config_callback)
        
        # Session variables
        self.session = None
        self.token = None
        self.client = None
        self.is_connected = False
        
        # UI state variables
        self.status_var = tk.StringVar(value="Disconnected")
        self.auto_refresh_timer_id = None
        self.refresh_count = 0
        self.api_restriction_warning_shown = False
        
        # Display variables (updated after signal refresh)
        self.last_speedtest_time = 0
        self.last_speedtest_dl = 0
        self.last_speedtest_ul = 0
        
        # Available bands (will be populated on connection)
        self.available_bands = {
            "4G": SUPPORTED_4G_BANDS,
            "5G": SUPPORTED_5G_BANDS
        }
        
        # Band selection variables - will be populated dynamically
        self.band_vars = {}
        # Initialize 4G bands
        for band_num in [1, 3, 7, 8, 20, 28, 32, 38, 40, 41, 42]:
            band = f"B{band_num}"
            self.band_vars[band] = tk.BooleanVar(value=band in self.config.get("selected_bands", []))
        
        # Initialize 5G bands
        for band_num in [1, 3, 28, 41, 78, 79]:
            band = f"n{band_num}"
            self.band_vars[band] = tk.BooleanVar(value=band in self.config.get("selected_bands", []))
        
        # Network aggregation variables
        self.upload_band_vars = {}
        self.download_band_vars = {}
        for band_num in [1, 3, 7, 8]:
            band = f"B{band_num}"
            self.upload_band_vars[band] = tk.BooleanVar(value=False)
            self.download_band_vars[band] = tk.BooleanVar(value=False)
        
        # Create the main layouts
        self.create_menu()
        self.create_main_frame()
        
        # Check for dependencies
        if not SPEEDTEST_AVAILABLE:
            self.log_message("Note: speedtest-cli not installed. Speed testing disabled.")
            self.log_message("Install with: pip install speedtest-cli")
        
        if not HUAWEI_API_AVAILABLE:
            self.log_message("Note: huawei-lte-api not installed. Advanced features disabled.")
            self.log_message("Install with: pip install huawei-lte-api")
        
        # Auto-connect if enabled
        if self.auto_connect.get():
            self.connect()
            # The _run_initial_speedtest will be called in handle_connection_result if speedtest_on_startup is enabled

    def create_menu(self):
        # Create top menu
        menu_bar = tk.Menu(self.root)
        
        file_menu = tk.Menu(menu_bar, tearoff=0)
        file_menu.add_command(label="Connect", command=self.connect)
        file_menu.add_command(label="Disconnect", command=self.disconnect)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menu_bar.add_cascade(label="File", menu=file_menu)
        
        tools_menu = tk.Menu(menu_bar, tearoff=0)
        tools_menu.add_command(label="Run Speed Test", command=self.start_speedtest)
        tools_menu.add_command(label="View Reports", command=self.view_reports)
        menu_bar.add_cascade(label="Tools", menu=tools_menu)
        
        help_menu = tk.Menu(menu_bar, tearoff=0)
        help_menu.add_command(label="How to Use", command=self.show_user_guide)
        help_menu.add_command(label="About", command=self.show_about)
        help_menu.add_command(label="Support the Project", command=self.show_donation_dialog)
        menu_bar.add_cascade(label="Help", menu=help_menu)
        
        self.root.config(menu=menu_bar)

    def create_main_frame(self):
        # Create a frame for the main content
        main_frame = ttk.Frame(self.root, padding="10")
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
            
        speedtest_startup_cb = ttk.Checkbutton(options_frame, text="Run Speedtest on Startup", variable=self.speedtest_on_startup)
        speedtest_startup_cb.pack(anchor=tk.W, pady=2)
        
        # Connect button
        connect_button = ttk.Button(conn_frame, text="Connect", command=self.connect)
        connect_button.grid(row=0, column=3, rowspan=3, padx=10)
        # Store as instance variable so it can be accessed elsewhere
        self.connect_button = connect_button
        
        # Create tooltip for connect button
        if TOOLTIPS_AVAILABLE:
            create_tooltip(connect_button, "Connect to your Huawei router using the provided IP address and credentials")
        
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
        
        refresh_button = ttk.Button(refresh_frame, text="Refresh Signal", command=self.refresh_signal)
        refresh_button.pack(side=tk.LEFT, padx=2)
        create_tooltip(refresh_button, "Refresh signal information to show current band, signal strength, and network type (4G/5G)")
        
        self.auto_refresh_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(refresh_frame, text="Auto-refresh", variable=self.auto_refresh_var, 
                         command=self.toggle_auto_refresh).pack(side=tk.LEFT, padx=5)
        
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
        
        apply_button = ttk.Button(band_buttons_frame, text="Apply Selection", 
                                command=self.apply_band_selection,
                                width=15)
        apply_button.pack(side=tk.LEFT, padx=2)
        create_tooltip(apply_button, "Apply the selected bands to your router - allows only the selected bands to be used")
        
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
        
        optimize_button = ttk.Button(action_grid, text="Optimise Bands", 
                                    command=self.optimise, width=18)
        optimize_button.grid(row=0, column=0, padx=2, pady=2, sticky="ew")
        create_tooltip(optimize_button, "Automatically test all frequency bands for both 4G and 5G connections. Evaluates signal quality metrics (RSRP, SINR) and recommends the best combination based on coverage and reliability.")
        
        enhanced_optimize_button = ttk.Button(action_grid, text="Enhanced Optimise", 
                                            command=self.enhanced_optimise, width=18)
        enhanced_optimize_button.grid(row=0, column=1, padx=2, pady=2, sticky="ew")
        create_tooltip(enhanced_optimize_button, "Advanced optimisation that tests all bands with both signal quality AND speed tests. Tests both 4G and 5G, runs actual speed tests for each band, and provides the most accurate recommendations.")
        
        speedtest_button = ttk.Button(action_grid, text="Speed Test", 
                                     command=self.start_improved_speedtest, width=18)
        speedtest_button.grid(row=1, column=0, padx=2, pady=2, sticky="ew")
        create_tooltip(speedtest_button, "Run a speed test using the current band configuration. Tests download and upload speeds using the nearest server.")
        
        view_reports_button = ttk.Button(action_grid, text="View Reports", 
                                        command=self.view_reports, width=18)
        view_reports_button.grid(row=1, column=1, padx=2, pady=2, sticky="ew")
        create_tooltip(view_reports_button, "View previously generated optimisation reports with detailed information about band tests and recommendations.")
        
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
        
        self.standard_log_text = tk.Text(standard_log_container, wrap=tk.WORD, height=15)
        self.standard_log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        standard_log_scrollbar = ttk.Scrollbar(standard_log_container, command=self.standard_log_text.yview)
        standard_log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.standard_log_text.config(yscrollcommand=standard_log_scrollbar.set)
        
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
        status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Initial log message
        self.log_message("Application started")
        self.log_message("Connect to your Huawei router to begin")

    def log_message(self, message, log_type="standard", replace_last=False):
        """Add a message to the log with timestamp
        
        Args:
            message: The message to log
            log_type: The type of log - 'standard', 'detailed', or 'both' (default: 'standard')
            replace_last: Whether to replace the last log message (for progress indicators)
        """
        timestamp = datetime.now().strftime("%H:%M:%S")
        formatted_message = f"[{timestamp}] {message}\n"
        
        # For technical/detailed messages only
        if log_type == "detailed":
            if replace_last:
                # Delete last line if replacing
                self.detailed_log_text.delete("end-2l", "end-1c")
            self.detailed_log_text.insert(tk.END, formatted_message)
            self.detailed_log_text.see(tk.END)
        # For user-friendly messages or both
        elif log_type == "standard" or log_type == "both":
            if replace_last:
                # Delete last line if replacing
                self.standard_log_text.delete("end-2l", "end-1c")
            self.standard_log_text.insert(tk.END, formatted_message)
            self.standard_log_text.see(tk.END)
            
            # Also add to detailed log if type is 'both'
            if log_type == "both":
                if replace_last:
                    # Delete last line if replacing
                    self.detailed_log_text.delete("end-2l", "end-1c")
                self.detailed_log_text.insert(tk.END, formatted_message)
                self.detailed_log_text.see(tk.END)
    
    def connect(self):
        """Connect to the router"""
        ip = self.router_ip.get()
        username = self.username.get()
        password = self.password.get()
        use_api_lib = self.use_api_lib.get()
        
        self.log_message(f"Connecting to {ip}...", log_type="both")
        self.status_var.set("Connecting...")
        
        # Clear previous connection
        if self.session or self.client:
            self.disconnect()
        
        # Run connection in a background thread to keep UI responsive
        def connect_thread():
            result = login_to_router(ip, username, password, use_api_lib)
            
            # Process results on the main thread
            self.root.after(0, lambda: self.handle_connection_result(result, ip))
        
        threading.Thread(target=connect_thread, daemon=True).start()
    
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
            self.config["speedtest_on_startup"] = self.speedtest_on_startup.get()
            save_config(self.config)
            
            # Update UI
            self.is_connected = True
            self.status_var.set("Connected")
            self.connect_button.config(text="Disconnect")
            
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
            if self.speedtest_on_startup.get():
                self._run_initial_speedtest()
        else:
            # Connection failed
            self.is_connected = False
            self.status_var.set("Not Connected")
            messagebox.showerror("Connection Failed", result[2])
            self.log_message(f"Connection failed: {result[2]}", log_type="both")
    
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
                    progress_task = self.root.after(500, lambda: update_progress(step + 1))
                
                # Start progress updates
                update_progress()
                
                # Run a standard speedtest
                result = run_speedtest()
                
                # Cancel progress updates
                if progress_task:
                    self.root.after_cancel(progress_task)
                
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
        # Cancel any pending auto-refresh
        if self.poll_status_task:
            self.root.after_cancel(self.poll_status_task)
            self.poll_status_task = None
        
        # Reset session
        self.session = None
        self.client = None
        self.token = None
        self.is_connected = False
        
        # Update UI
        self.log_message("Disconnected from router", log_type="both")
        self.status_var.set("Disconnected")
        
        # Reset signal info
        for key in self.signal_info:
            self.signal_info[key].set("--")
    
    def refresh_signal(self):
        """Refresh signal data"""
        if not self.is_connected:
            self.log_message("Not connected. Cannot refresh signal.")
            return
        
        self.log_message("Refreshing signal data...", log_type="both")
        
        # Run in background thread to keep UI responsive
        def refresh_thread():
            # Use the unified fetch_signal_data function
            signal_data = fetch_signal_data(self, self.session or self.client, self.router_ip.get(), self.token)
            
            # Update UI on main thread
            self.root.after(0, lambda: self.update_signal_ui(signal_data))
        
        threading.Thread(target=refresh_thread, daemon=True).start()
    
    def update_signal_ui(self, signal_data):
        """Update UI with signal data"""
        if not signal_data:
            self.log_message("Failed to get signal data", log_type="both")
            return
        
        # Store signal data
        self.signal_data = signal_data
        
        # Log raw signal data to detailed log only
        self.log_message(f"Device signal data: {self.signal_data}", log_type="detailed")
        
        # Check for multiple bands (indicating carrier aggregation)
        band_value = signal_data.get("BAND", "")
        network_type = signal_data.get("NETWORK_TYPE", "")
        
        # Parse the bands the router is currently connected to
        current_bands = []
        if band_value:
            if "," in band_value:
                current_bands = [b.strip() for b in band_value.split(",")]
            else:
                current_bands = [band_value.strip()]
        
        # Update the band_vars to reflect the current bands if we have the band checkboxes created
        if hasattr(self, 'band_vars') and current_bands:
            self.log_message(f"Syncing UI with currently connected bands: {', '.join(current_bands)}", log_type="detailed")
            # First, clear all band selections
            for band, var in self.band_vars.items():
                var.set(False)
            
            # Then select the current bands
            for band in current_bands:
                if band in self.band_vars:
                    self.band_vars[band].set(True)
                    self.log_message(f"Selected band {band} in UI", log_type="detailed")
        
        # Check if router speed data should be used or preserved from a recent speedtest
        router_dl_speed = signal_data.get("DOWNLOAD", "--")
        router_ul_speed = signal_data.get("UPLOAD", "--")
        
        # Extract numeric values for comparison
        try:
            router_dl_value = float(router_dl_speed.split()[0]) if isinstance(router_dl_speed, str) and " " in router_dl_speed else 0
            router_ul_value = float(router_ul_speed.split()[0]) if isinstance(router_ul_speed, str) and " " in router_ul_speed else 0
        except (ValueError, IndexError):
            router_dl_value = 0
            router_ul_value = 0
        
        # Only update speeds from router if no recent speedtest or if router speeds are higher
        # This prevents the confusing situation where speedtest shows high speeds but signal refresh shows low speeds
        if hasattr(self, 'last_speedtest_time') and hasattr(self, 'last_speedtest_dl') and hasattr(self, 'last_speedtest_ul'):
            time_since_speedtest = time.time() - self.last_speedtest_time
            
            # If speedtest was run within the last 5 minutes and had higher speeds than router is reporting
            if time_since_speedtest < 300:  # 5 minutes in seconds
                dl_speed = f"{self.last_speedtest_dl:.2f} Mbps (speedtest)" if self.last_speedtest_dl > router_dl_value else router_dl_speed
                ul_speed = f"{self.last_speedtest_ul:.2f} Mbps (speedtest)" if self.last_speedtest_ul > router_ul_value else router_ul_speed
                
                # Update the signal data with speedtest values if they're higher
                signal_data["DOWNLOAD"] = dl_speed
                signal_data["UPLOAD"] = ul_speed
        
        # Update signal info display
        for key, value in signal_data.items():
            if key in self.signal_info:
                self.signal_info[key].set(value or "--")  # Ensure None values are displayed as "--"
        
        # Apply more user-friendly network type names
        if "," in band_value and "LTE" in network_type and not "LTE-CA" in network_type:
            self.signal_info["NETWORK_TYPE"].set("LTE-CA (4G+)")
            network_type = "LTE-CA (4G+)"
        elif network_type == "LTE":
            self.signal_info["NETWORK_TYPE"].set("4G")
            network_type = "4G"
        
        # Format user-friendly network display
        if network_type == "LTE":
            network_display = "4G"
        elif network_type == "LTE-CA (4G+)":
            network_display = "4G+"
        elif "5G" in network_type:
            network_display = network_type  # Keep 5G as is
        else:
            network_display = network_type
            
        # Get signal values for user-friendly presentation - protect against None values
        rsrp_raw = signal_data.get("RSRP", "--") or "--"
        rsrp = rsrp_raw.replace("dBm", "") if isinstance(rsrp_raw, str) else "--"
        
        sinr_raw = signal_data.get("SINR", "--") or "--"
        sinr = sinr_raw.replace("dB", "") if isinstance(sinr_raw, str) else "--"
        
        carrier = signal_data.get("CARRIER", "--") or "--"
        dl_speed = signal_data.get("DOWNLOAD", "--") or "--"
        ul_speed = signal_data.get("UPLOAD", "--") or "--"
        
        # Determine signal quality description
        try:
            rsrp_value = float(rsrp) if rsrp != "--" else -100
        except ValueError:
            rsrp_value = -100
        
        if rsrp_value >= -80:
            signal_quality = "Excellent"
        elif rsrp_value >= -90:
            signal_quality = "Good"
        elif rsrp_value >= -100:
            signal_quality = "Fair"
        elif rsrp_value >= -110:
            signal_quality = "Poor"
        else:
            signal_quality = "Very Poor"
        
        # Format band info nicely
        if "," in band_value:
            bands_list = [b.strip() for b in band_value.split(",")]
            band_display = f"{len(bands_list)} bands: {', '.join(bands_list)}"
        else:
            band_display = band_value
        
        # Create a user-friendly summary for standard log
        self.log_message(f"📡 Connection: {network_display} on {band_display} ({carrier})", log_type="standard")
        self.log_message(f"📊 Signal: {signal_quality} (RSRP: {rsrp} dBm, SINR: {sinr} dB)", log_type="standard")
        
        # Show current speeds from router (these will be updated by the initial speedtest if run)
        self.log_message(f"⚡ Current speeds: {dl_speed} down, {ul_speed} up", log_type="standard")
        
        # Check connection status
        if self.client:
            try:
                status = get_connection_status(self.client, self.router_ip.get(), None)
                
                # Log detailed network information to detailed tab only
                self.log_message(f"Network mode: {status.get('network_mode', {})}", log_type="detailed")
                self.log_message(f"PLMN info: {status.get('plmn_info', {})}", log_type="detailed")
                self.log_message(f"Traffic stats: {status.get('traffic_stats', {})}", log_type="detailed")
                self.log_message(f"Status info: {status.get('status_info', {})}", log_type="detailed")
                
                # Log parsed signal data to detailed tab
                self.log_message(f"API - Parsed signal data: {signal_data}", log_type="detailed")
                
                network_type_status = status.get("network_type", "Unknown")
                
                # Format for display
                if network_type_status == "LTE":
                    network_display = "4G"
                elif network_type_status == "LTE-CA (4G+)":
                    network_display = "4G+"
                elif "5G" in network_type_status:
                    network_display = network_type_status
                else:
                    network_display = network_type_status
                
                self.status_var.set(f"Connected: {network_display}")
            except Exception as e:
                self.log_message(f"Error getting status: {str(e)}", log_type="both")
    
    def toggle_auto_refresh(self):
        """Toggle automatic signal refresh"""
        if self.auto_refresh_var.get():
            self.log_message("Auto-refresh enabled", log_type="both")
            self.poll_status()
        else:
            self.log_message("Auto-refresh disabled", log_type="both")
            if self.poll_status_task:
                self.root.after_cancel(self.poll_status_task)
                self.poll_status_task = None
    
    def poll_status(self):
        """Poll signal status at regular intervals"""
        if self.is_connected:
            self.refresh_signal()
        
        # Schedule next update
        self.poll_status_task = self.root.after(self.signal_update_interval, self.poll_status)
    
    def apply_band_selection(self):
        """Apply the selected bands to the router"""
        if not self.is_connected:
            self.log_message("Not connected. Cannot apply band selection.", log_type="both")
            return
        
        # Get selected bands
        selected_bands = []
        
        for band, var in self.band_vars.items():
            if var.get():
                selected_bands.append(band)
        
        if not selected_bands:
            self.log_message("No bands selected.", log_type="both")
            return
        
        band_list = ", ".join([f"B{band}" for band in selected_bands])
        self.log_message(f"Applying band selection: {band_list}...", log_type="both")
        
        # Run in background thread to keep UI responsive
        def apply_thread():
            success = apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, selected_bands)
            
            if success:
                self.root.after(0, lambda: self.log_message("Band selection applied successfully. Changes may take up to 30 seconds to take effect.", log_type="both"))
                self.root.after(5000, self.refresh_signal)  # Refresh after a delay
            else:
                self.root.after(0, lambda: self.log_message("Failed to apply band selection. Check connection.", log_type="both"))
        
        threading.Thread(target=apply_thread, daemon=True).start()
    
    def apply_network_config(self):
        """Apply network aggregation configuration"""
        # Implementation will be added here
        pass
    
    def apply_network_mode(self):
        """Apply network mode selection"""
        # Implementation will be added here
        pass
    
    def toggle_all_bands(self, state, band_type=None):
        """Select or deselect all bands
        
        Args:
            state: True to select all, False to deselect all
            band_type: Optional, '4G' or '5G' to toggle only that type, or None for all bands
        """
        if band_type is None:
            # Toggle all bands
            for band, band_var in self.band_vars.items():
                band_var.set(state)
        elif band_type == '4G':
            # Toggle only 4G bands (starting with 'B')
            for band, band_var in self.band_vars.items():
                if band.startswith('B'):
                    band_var.set(state)
        elif band_type == '5G':
            # Toggle only 5G bands (starting with 'n')
            for band, band_var in self.band_vars.items():
                if band.startswith('n'):
                    band_var.set(state)
    
    def optimise(self):
        """Optimise band selection based on signal strength"""
        if not self.is_connected:
            self.log_message("⚠️ Not connected. Cannot optimise bands.", log_type="both")
            return
        
        self.log_message("🔍 Starting band optimisation...", log_type="both")
        self.log_message("This process will test all available bands and recommend the best combination.", log_type="standard")
        
        # Save current band configuration before starting
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(band)
        
        self.log_message(f"Current band config saved: {', '.join(original_band_config) if original_band_config else 'No bands'}", log_type="detailed")
        
        # Run in background thread to keep UI responsive
        def optimise_thread():
            """Run the optimisation process in a background thread"""
            try:
                # Test each band one by one
                results = {}
                
                # Test each band one by one - use available bands
                bands_to_test = self.available_bands["4G"]
                
                for band in bands_to_test:
                    self.log_message(f"🔄 Testing band {band}...", log_type="standard")
                    self.log_message(f"Testing band {band}...", log_type="detailed")
                    
                    # Apply the band selection
                    apply_band_lock(self.session or self.client, self.router_ip.get(), self.token, [band])
                    
                    # Wait for connection to stabilize
                    time.sleep(12)
                    
                    # Refresh signal data
                    signal_data = fetch_signal_data(self, self.session or self.client, self.router_ip.get(), self.token)
                    
                    if not signal_data:
                        self.log_message(f"⚠️ Failed to get signal data for band {band}", log_type="both")
                        results[band] = {"score": 0, "rsrp": None, "sinr": None, "failed": True}
                        continue
                    
                    # Send to detailed log
                    self.log_message(f"Band {band} signal data: {signal_data}", log_type="detailed")
                    
                    # Get signal metrics
                    rsrp = signal_data.get("RSRP", "-120dBm")
                    if isinstance(rsrp, str) and "dBm" in rsrp:
                        rsrp = rsrp.replace("dBm", "")
                    rsrp_float = float(rsrp)
                    
                    sinr = signal_data.get("SINR", "0dB")
                    if isinstance(sinr, str) and "dB" in sinr:
                        sinr = sinr.replace("dB", "")
                    sinr_float = float(sinr)
                    
                    # Simple scoring algorithm considering RSRP and SINR
                    # RSRP range: -140 to -44 (higher is better)
                    # SINR range: -20 to 30 (higher is better)
                    
                    # Normalize RSRP to 0-100 range where 100 is best (-44dBm) and 0 is worst (-140dBm)
                    rsrp_norm = max(0, min(100, (rsrp_float + 140) / 96 * 100))
                    
                    # Normalize SINR to 0-100 range where 100 is best (30dB) and 0 is worst (-20dB)
                    sinr_norm = max(0, min(100, (sinr_float + 20) / 50 * 100))
                    
                    # Final score with more weight on RSRP (60%) than SINR (40%)
                    score = 0.6 * rsrp_norm + 0.4 * sinr_norm
                    
                    network_type = signal_data.get("NETWORK_TYPE", "4G")
                    
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
                
                # Generate report
                report_path = generate_report(results, "basic")

                # Find top bands
                sorted_bands = sorted(results.items(), key=lambda x: x[1]["score"], reverse=True)
                top_bands = [band for band, data in sorted_bands if data["score"] > 0][:3]
                
                if not top_bands:
                    self.log_message("⚠️ No usable bands found. Try again or check connection.", log_type="both")
                    return
                
                # Show optimisation summary dialogue
                self.root.after(0, lambda: self.show_optimisation_summary(top_bands, results, report_path))
                
                # Play notification sound
                self.root.bell()
            except Exception as e:
                self.log_message(f"Optimisation error: {str(e)}", log_type="both")
                
            finally:
                # Always try to restore original bands if we have them
                try:
                    if original_band_config:
                        apply_band_lock(
                            self.session or self.client,
                            self.router_ip.get(),
                            self.token,
                            original_band_config
                        )
                except:
                    pass
        
        threading.Thread(target=optimise_thread, daemon=True).start()
    
    def enhanced_optimise(self):
        """Run enhanced optimisation with speed tests"""
        # Save current band configuration before starting
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(f"B{band}")
        
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
                    band_num = int(band.replace("B", ""))
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
                    band_num = int(band.replace("n", ""))
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
                recommended_results["4G"] = [f"B{band}" for band, _ in sorted_4g[:2]]
            
            # Get best 5G band if available
            if results_5g:
                sorted_5g = sorted(results_5g.items(), key=lambda x: x[1]["score"], reverse=True)
                if sorted_5g:
                    recommended_results["5G"] = [f"n{band}" for band, _ in sorted_5g[:1]]
            
            # Generate report
            report_path = generate_report({
                '4G_results': results_4g,
                '5G_results': results_5g,
                'recommended': recommended_results
            }, optimisation_type="enhanced")
            
            # Show results summary
            self.root.after(0, lambda: self.show_enhanced_optimisation_summary(
                results_4g, results_5g, recommended_results, report_path
            ))
            
            # Play notification sound
            self.root.bell()
            
        except Exception as e:
            self.log_message(f"Enhanced optimisation error: {str(e)}", log_type="both")
            # Attempt to restore original bands
            try:
                if original_band_config:
                    self.apply_band_selection(original_band_config)
            except Exception as restore_error:
                self.log_message(f"Failed to restore original bands: {str(restore_error)}", log_type="both")
    
    def show_enhanced_optimisation_summary(self, results_4g, results_5g, recommended_results, report_path):
        """Show enhanced optimisation summary with separate 4G and 5G results"""
        # Get original band config
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(f"B{band}")
                
        # Create dialogue
        dialogue = tk.Toplevel(self.root)
        dialogue.title("Enhanced Optimisation Results")
        dialogue.geometry("800x600")  # Made wider and taller for more content
        dialogue.transient(self.root)
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
                    self.root.after(0, lambda: self.log_message("✅ 4G configuration applied successfully!", log_type="both"))
                    
                    # Update band selection checkboxes
                    for band_num, var in self.band_vars.items():
                        band_str = f"B{band_num}"
                        self.root.after(0, lambda bn=band_str, v=var: 
                            v.set(bn in recommended_results['4G']['bands']))
                    
                    self.root.after(5000, self.refresh_signal)
                else:
                    self.root.after(0, lambda: self.log_message("❌ Failed to apply 4G configuration.", log_type="both"))
            
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
                    self.root.after(0, lambda: self.log_message("✅ 5G configuration applied successfully!", log_type="both"))
                    
                    # Update band selection checkboxes
                    for band_num, var in self.band_vars.items():
                        band_str = f"B{band_num}"
                        self.root.after(0, lambda bn=band_str, v=var: 
                            v.set(bn in recommended_results['5G']['bands']))
                    
                    self.root.after(5000, self.refresh_signal)
                else:
                    self.root.after(0, lambda: self.log_message("❌ Failed to apply 5G configuration.", log_type="both"))
            
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
                        self.root.after(0, lambda: self.log_message("✅ Original configuration restored", log_type="both"))
                        
                        # Update band selection checkboxes
                        for band_num, var in self.band_vars.items():
                            band_str = f"B{band_num}"
                            self.root.after(0, lambda bn=band_str, v=var: v.set(bn in original_band_config))
                        
                        self.root.after(5000, self.refresh_signal)
                    else:
                        self.root.after(0, lambda m=msg: self.log_message(f"❌ Failed to restore configuration: {m}", log_type="both"))
                
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
        dialog = tk.Toplevel(self.root)
        dialog.title("Support the Project")
        dialog.geometry("400x300")
        dialog.transient(self.root)
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

    def view_report(self, report_path):
        """Open a specific report file in a dialogue."""
        if not os.path.exists(report_path):
            messagebox.showerror("Error", "Report file not found.")
            return
        
        # Read report content
        try:
            with open(report_path, 'r') as f:
                report_content = f.read()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to read report: {str(e)}")
            return
        
        # Create dialogue to display report
        dialogue = tk.Toplevel(self.root)
        dialogue.title("Report Viewer")
        dialogue.geometry("700x500")
        dialogue.transient(self.root)
        dialogue.grab_set()
        
        # Report content
        text_frame = tk.Frame(dialogue)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        text_widget = tk.Text(text_frame, wrap=tk.WORD)
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        scrollbar = tk.Scrollbar(text_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        text_widget.config(yscrollcommand=scrollbar.set)
        scrollbar.config(command=text_widget.yview)
        
        # Insert report content
        text_widget.insert(tk.END, report_content)
        text_widget.config(state=tk.DISABLED)  # Make read-only
        
        # Buttons
        button_frame = tk.Frame(dialogue)
        button_frame.pack(fill=tk.X, pady=10)
        
        # Close button
        close_button = tk.Button(button_frame, text="Close", command=dialogue.destroy)
        close_button.pack(side=tk.RIGHT, padx=10)
        
        # Export button
        def on_export():
            export_path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
                initialfile=os.path.basename(report_path)
            )
            if export_path:
                try:
                    with open(report_path, 'r') as src, open(export_path, 'w') as dst:
                        dst.write(src.read())
                    messagebox.showinfo("Export", "Report exported successfully")
                except Exception as e:
                    messagebox.showerror("Error", f"Failed to export report: {str(e)}")
        
        export_button = tk.Button(button_frame, text="Export", command=on_export)
        export_button.pack(side=tk.RIGHT, padx=10)
    
    def view_reports(self):
        """View list of generated reports"""
        # Get list of reports
        reports_dir = ensure_reports_dir()
        reports = [f for f in os.listdir(reports_dir) if f.startswith("optimisation_report_") and f.endswith(".txt")]
        
        if not reports:
            messagebox.showinfo("No Reports", "No optimisation reports found. Run an optimisation first.")
            return
        
        # Create a dialogue to select a report
        dialogue = tk.Toplevel(self.root)
        dialogue.title("Select Report")
        dialogue.geometry("400x300")
        dialogue.transient(self.root)
        dialogue.grab_set()
        
        # Sort reports by date (newest first)
        reports.sort(reverse=True)
        
        # Create listbox with reports
        listbox = tk.Listbox(dialogue, width=50, height=15)
        listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        for report in reports:
            # Make display name more friendly
            display_name = report.replace("optimisation_report_", "").replace(".txt", "").replace("_", " ")
            listbox.insert(tk.END, display_name)
        
        # Add scrollbar
        scrollbar = tk.Scrollbar(listbox)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        listbox.config(yscrollcommand=scrollbar.set)
        scrollbar.config(command=listbox.yview)
        
        # Buttons frame
        button_frame = tk.Frame(dialogue)
        button_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # View button
        def on_view():
            selection = listbox.curselection()
            if selection:
                report_name = reports[selection[0]]
                report_path = os.path.join(reports_dir, report_name)
                self.view_report(report_path)
                dialogue.destroy()
                
        # Open folder button
        def on_open_folder():
            try:
                # Open the reports folder in explorer/finder
                if platform.system() == "Windows":
                    os.startfile(reports_dir)
                elif platform.system() == "Darwin":  # macOS
                    subprocess.call(["open", reports_dir])
                else:  # Linux
                    subprocess.call(["xdg-open", reports_dir])
            except Exception as e:
                messagebox.showerror("Error", f"Could not open reports folder: {str(e)}")
            dialogue.destroy()
        
        view_button = tk.Button(button_frame, text="View Report", command=on_view)
        view_button.pack(side=tk.LEFT, padx=5)
        
        folder_button = tk.Button(button_frame, text="Open Reports Folder", command=on_open_folder)
        folder_button.pack(side=tk.LEFT, padx=5)
        
        cancel_button = tk.Button(button_frame, text="Cancel", command=dialogue.destroy)
        cancel_button.pack(side=tk.RIGHT, padx=5)

    # Add a new method to run speedtest with a specific Coventry server
    def start_improved_speedtest(self):
        """Run a speed test with improved settings for better accuracy"""
        if not SPEEDTEST_AVAILABLE:
            self.log_message("⚠️ speedtest-cli not installed. Install with: pip install speedtest-cli", log_type="both")
            return
        
        self.log_message("🔄 Starting speed test (this may take a minute)...", log_type="both")
        
        # Run in background thread to keep UI responsive
        def speedtest_thread():
            try:
                # Get signal info for efficiency calculation
                network_type = self.signal_info.get("NETWORK_TYPE", tk.StringVar(value="Unknown")).get()
                current_band = self.signal_info.get("BAND", tk.StringVar(value="Unknown")).get()
                rsrp = self.signal_info.get("RSRP", tk.StringVar(value="-100")).get()
                sinr = self.signal_info.get("SINR", tk.StringVar(value="10")).get()
                
                # Extract first band if multiple
                if "," in current_band:
                    first_band = current_band.split(",")[0].strip()
                else:
                    first_band = current_band.strip()
                
                # Get theoretical speeds
                try:
                    theoretical_dl, theoretical_ul = estimate_max_speed(
                        first_band, network_type, rsrp, sinr)
                except Exception as e:
                    self.log_message(f"Error estimating theoretical speeds: {str(e)}", log_type="detailed")
                    theoretical_dl, theoretical_ul = 0, 0
                
                # Find best server by location
                self.log_message("Finding optimal test server...", log_type="standard")
                st = speedtest.Speedtest()
                st.get_servers()
                server = st.get_best_server()
                self.log_message(f"Selected server: {server['name']} ({server['sponsor']} - {server['country']})", log_type="standard")
                
                # Run the speed test with best server
                self.log_message("⬇️ Testing download speed...", log_type="standard")
                result = run_speedtest()
                
                # Log detailed speedtest result to detailed log
                self.log_message(f"Detailed speedtest result: {result}", log_type="detailed")
                
                if result["success"]:
                    dl = result["download"]
                    ul = result["upload"]
                    ping = result["ping"]
                    server = result["server"]
                    server_id = result.get("server_id", "Unknown")
                    server_host = result.get("server_host", "Unknown")
                    upload_attempts = result.get("upload_attempts", [])
                    
                    # Save speedtest results for use in update_signal_ui
                    self.last_speedtest_time = time.time()
                    self.last_speedtest_dl = dl
                    self.last_speedtest_ul = ul
                    
                    # Update signal information with the new speed values
                    self.signal_info["DOWNLOAD"].set(f"{dl:.2f} Mbps")
                    self.signal_info["UPLOAD"].set(f"{ul:.2f} Mbps")
                    
                    # Calculate efficiency if theoretical speeds are available
                    if theoretical_dl > 0:
                        dl_efficiency = (dl / theoretical_dl) * 100
                        dl_efficiency_str = f" ({dl_efficiency:.1f}% of theoretical max)"
                    else:
                        dl_efficiency_str = ""
                    
                    if theoretical_ul > 0:
                        ul_efficiency = (ul / theoretical_ul) * 100
                        ul_efficiency_str = f" ({ul_efficiency:.1f}% of theoretical max)"
                    else:
                        ul_efficiency_str = ""
                    
                    # Check if multiple bands are in use (indicating carrier aggregation/4G+)
                    if "," in current_band and "LTE" in network_type and not "LTE-CA" in network_type:
                        network_type = "LTE-CA (4G+)"
                    
                    # Format network display name
                    if network_type == "LTE":
                        network_display = "4G"
                    elif network_type == "LTE-CA (4G+)":
                        network_display = "4G+"
                    elif "5G" in network_type:
                        network_display = network_type  # Keep 5G as is
                    else:
                        network_display = network_type
                    
                    # Create user-friendly message for standard log
                    standard_message = (
                        f"📊 Speed test results [{network_display}]:\n"
                        f"⬇️ Download: {dl:.2f} Mbps{dl_efficiency_str}\n"
                        f"⬆️ Upload: {ul:.2f} Mbps{ul_efficiency_str}\n"
                        f"🔄 Ping: {ping:.2f} ms\n"
                        f"🖥️ Server: {server}\n"
                        f"📡 Band: {current_band}"
                    )
                    
                    # Create detailed message with additional technical info
                    detailed_message = (
                        f"Speed test results [{network_display}]:\n"
                        f"Download: {dl:.2f} Mbps{dl_efficiency_str}\n"
                        f"Upload: {ul:.2f} Mbps{ul_efficiency_str}\n"
                        f"Ping: {ping:.2f} ms\n"
                        f"Server: {server} (ID: {server_id}, Host: {server_host})\n"
                        f"Current band: {current_band}"
                    )
                    
                    if theoretical_dl > 0:
                        detailed_message += f"\nTheoretical maximum: {theoretical_dl:.2f} Mbps download, {theoretical_ul:.2f} Mbps upload"
                    
                    # Show upload attempts if we have them
                    if upload_attempts:
                        attempts_str = ", ".join([f"{speed:.2f}" for speed in upload_attempts])
                        detailed_message += f"\nUpload attempts (Mbps): {attempts_str} - Multiple tests run for more accurate upload measurement"
                        
                    # Log messages to both logs
                    self.root.after(0, lambda: self.log_message(standard_message, log_type="standard"))
                    self.root.after(0, lambda: self.log_message(detailed_message, log_type="detailed"))
                    
                    # Also refresh the signal display with new speed values
                    self.refresh_signal()
                else:
                    self.root.after(0, lambda: self.log_message(f"⚠️ Speed test failed: {result['message']}", log_type="both"))
            except Exception as e:
                self.root.after(0, lambda: self.log_message(f"⚠️ Speed test error: {str(e)}", log_type="both"))
        
        threading.Thread(target=speedtest_thread, daemon=True).start()

    def show_optimisation_summary(self, selected_bands, results, report_path):
        """Show optimisation summary with apply/cancel buttons"""
        # Get original band config from the optimise method
        original_band_config = []
        for band, var in self.band_vars.items():
            if var.get():
                original_band_config.append(f"B{band}")
                
        # Create dialogue
        dialogue = tk.Toplevel(self.root)
        dialogue.title("Optimisation Results")
        dialogue.geometry("500x400")
        dialogue.transient(self.root)
        dialogue.grab_set()
        
        # Create summary frame
        summary_frame = ttk.Frame(dialogue, padding="10")
        summary_frame.pack(fill=tk.BOTH, expand=True)
        
        # Header
        ttk.Label(summary_frame, text="Optimisation Results", 
                  font=("TkDefaultFont", 12, "bold")).pack(pady=(0, 10))
        
        # Create text area for results
        text_area = tk.Text(summary_frame, wrap=tk.WORD, height=15)
        text_area.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        scroll = ttk.Scrollbar(summary_frame, command=text_area.yview)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)
        text_area.config(yscrollcommand=scroll.set)
        
        # Add summary content
        summary = f"📊 Recommended Band Combination: {', '.join(selected_bands)}\n\n"
        summary += "🏆 Top Band Results:\n\n"
        
        # Show top 5 bands (or fewer if less available)
        for i, band in enumerate(selected_bands[:min(5, len(selected_bands))]):
            band_num = int(band.replace("B", ""))
            band_data = results.get(band_num, {})
            
            rsrp = band_data.get("rsrp", "Unknown")
            sinr = band_data.get("sinr", "Unknown")
            score = band_data.get("score", 0)
            network_type = band_data.get("network_type", "4G")
            
            if rsrp != "Unknown":
                summary += f"Band {band} ({network_type}):\n"
                summary += f"  Signal: RSRP {rsrp} dBm, SINR {sinr} dB\n"
                summary += f"  Signal Score: {score:.1f}\n\n"
        
        # Add explanation of the next steps
        summary += "⚠️ IMPORTANT: Click 'Apply These Settings' to use the recommended bands,\n"
        summary += "or 'Cancel' to keep your current settings.\n\n"
        summary += f"A detailed report has been saved to:\n{report_path}"
        
        text_area.insert(tk.END, summary)
        text_area.config(state=tk.DISABLED)  # Make read-only
        
        # Button frame
        button_frame = ttk.Frame(dialogue, padding="10")
        button_frame.pack(fill=tk.X)
        
        def on_apply():
            # Apply the selected bands
            self.log_message(f"🔄 Applying optimal bands: {', '.join(selected_bands)}", log_type="both")
            
            def apply_thread():
                success = apply_band_lock(
                    self.session or self.client,
                    self.router_ip.get(),
                    self.token,
                    selected_bands
                )
                
                if success:
                    self.root.after(0, lambda: self.log_message("✅ Optimisation complete!", log_type="both"))
                    
                    # Update band selection checkboxes
                    for band_num, var in self.band_vars.items():
                        band_str = f"B{band_num}"
                        self.root.after(0, lambda bn=band_str, v=var: v.set(bn in selected_bands))
                    
                    self.root.after(5000, self.refresh_signal)  # Refresh after a delay
                else:
                    self.root.after(0, lambda: self.log_message("❌ Failed to apply band selection. Check connection.", log_type="both"))
            
            threading.Thread(target=apply_thread, daemon=True).start()
            dialogue.destroy()
        
        def on_cancel():
            self.log_message("Optimisation cancelled. Restoring original band configuration.", log_type="both")
            
            # Restore original band configuration
            if original_band_config:
                def restore_thread():
                    self.log_message(f"Restoring bands: {', '.join(original_band_config)}", log_type="detailed")
                    success = apply_band_lock(
                        self.session or self.client,
                        self.router_ip.get(),
                        self.token,
                        original_band_config
                    )
                    
                    if success:
                        self.root.after(0, lambda: self.log_message("✅ Original band configuration restored", log_type="both"))
                        
                        # Update band selection checkboxes
                        for band_num, var in self.band_vars.items():
                            band_str = f"B{band_num}"
                            self.root.after(0, lambda bn=band_str, v=var: v.set(bn in original_band_config))
                        
                        self.root.after(5000, self.refresh_signal)  # Refresh after a delay
                    else:
                        self.root.after(0, lambda: self.log_message("❌ Failed to restore original configuration", log_type="both"))
                
                threading.Thread(target=restore_thread, daemon=True).start()
            else:
                self.log_message("No previous configuration to restore", log_type="detailed")
            
            dialogue.destroy()

        def view_report():
            self.view_report(report_path)
        
        ttk.Button(button_frame, text="Apply These Settings", command=on_apply).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="View Report", command=view_report).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=on_cancel).pack(side=tk.RIGHT, padx=5)

    def save_config_callback(self, *args):
        """Save configuration when checkbox values change"""
        self.config["router_ip"] = self.router_ip.get()
        self.config["username"] = self.username.get()
        self.config["password"] = self.password.get()
        self.config["auto_connect"] = self.auto_connect.get()
        self.config["use_api_lib"] = self.use_api_lib.get()
        self.config["speedtest_on_startup"] = self.speedtest_on_startup.get()
        save_config(self.config)
        self.log_message(f"Settings saved", log_type="detailed")

    def save_speedtest_results(self, download, upload):
        """Save speedtest results for use in signal display"""
        self.last_speedtest_time = time.time()
        self.last_speedtest_dl = download
        self.last_speedtest_ul = upload
        
        # Update signal information with the new speed values
        self.signal_info["DOWNLOAD"].set(f"{download:.2f} Mbps")
        self.signal_info["UPLOAD"].set(f"{upload:.2f} Mbps")

    def update_band_selection_ui(self):
        """Update band selection UI based on available bands"""
        # Clear existing band vars
        self.band_vars.clear()
        
        # Create new band vars for available 4G bands
        for band in self.available_bands["4G"]:
            self.band_vars[band] = tk.BooleanVar(value=band in self.config.get("selected_bands", []))
            
        # Create new band vars for available 5G bands
        for band in self.available_bands["5G"]:
            self.band_vars[band] = tk.BooleanVar(value=band in self.config.get("selected_bands", []))
        
        # Log available bands for debugging
        self.log_message(f"Updating band UI with 4G bands: {', '.join(self.available_bands['4G'])}", log_type="detailed")
        self.log_message(f"Updating band UI with 5G bands: {', '.join(self.available_bands['5G'])}", log_type="detailed")
        
        # Custom band sorting function (sorts numerically instead of alphabetically)
        def sort_bands(band_name):
            # Extract the numeric part from the band name (e.g., "B1" -> 1, "n71" -> 71)
            if band_name.startswith('B'):
                return int(band_name[1:])
            elif band_name.startswith('n'):
                return int(band_name[1:])
            else:
                return 0  # Fallback for unknown formats
        
        # Check if we have the band section tabs
        if hasattr(self, 'band_section_4g') and hasattr(self, 'band_section_5g'):
            # Update 4G bands tab
            # First, clear all existing widgets from the section
            for child in self.band_section_4g.winfo_children():
                child.destroy()
            
            # Create new checkboxes for available 4G bands
            # Group into rows of 4
            row = 0
            col = 0
            # Sort bands numerically instead of alphabetically
            for band in sorted(self.available_bands["4G"], key=sort_bands):
                checkbox = ttk.Checkbutton(self.band_section_4g, text=band, 
                                          variable=self.band_vars[band])
                checkbox.grid(row=row, column=col, sticky=tk.W, padx=2, pady=1)
                col += 1
                if col >= 4:
                    col = 0
                    row += 1
            
            # Add control buttons at the bottom
            band_buttons_4g = ttk.Frame(self.band_section_4g)
            band_buttons_4g.grid(row=row+1, column=0, columnspan=4, pady=5)
            
            ttk.Button(band_buttons_4g, text="Select All 4G", 
                      command=lambda: self.toggle_all_bands(True, '4G'),
                      width=12).pack(side=tk.LEFT, padx=2)
                      
            ttk.Button(band_buttons_4g, text="Clear All 4G", 
                      command=lambda: self.toggle_all_bands(False, '4G'),
                      width=12).pack(side=tk.LEFT, padx=2)
            
            # Update 5G bands tab
            # First, clear all existing widgets from the section
            for child in self.band_section_5g.winfo_children():
                child.destroy()
            
            # Create new checkboxes for available 5G bands
            # Group into rows of 4
            row = 0
            col = 0
            # Sort bands numerically instead of alphabetically
            for band in sorted(self.available_bands["5G"], key=sort_bands):
                checkbox = ttk.Checkbutton(self.band_section_5g, text=band, 
                                          variable=self.band_vars[band])
                checkbox.grid(row=row, column=col, sticky=tk.W, padx=2, pady=1)
                col += 1
                if col >= 4:
                    col = 0
                    row += 1
            
            # Add control buttons at the bottom
            band_buttons_5g = ttk.Frame(self.band_section_5g)
            band_buttons_5g.grid(row=row+1, column=0, columnspan=4, pady=5)
            
            ttk.Button(band_buttons_5g, text="Select All 5G", 
                      command=lambda: self.toggle_all_bands(True, '5G'),
                      width=12).pack(side=tk.LEFT, padx=2)
                      
            ttk.Button(band_buttons_5g, text="Clear All 5G", 
                      command=lambda: self.toggle_all_bands(False, '5G'),
                      width=12).pack(side=tk.LEFT, padx=2)
            
            self.log_message("Band selection updated with available bands", log_type="both")
        else:
            self.log_message("Could not find band selection UI - please restart the application", log_type="both")

    def show_user_guide(self):
        """Show the user guide dialog"""
        # Create user guide dialog
        dialog = tk.Toplevel(self.root)
        dialog.title("User Guide - Huawei Band Optimiser")
        dialog.geometry("700x500")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Create a notebook for tabbed sections of the guide
        notebook = ttk.Notebook(dialog)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Getting Started tab
        getting_started = ttk.Frame(notebook)
        notebook.add(getting_started, text="Getting Started")
        
        ttk.Label(getting_started, text="Getting Started with Huawei Band Optimiser", 
                 font=("TkDefaultFont", 12, "bold")).pack(pady=10)
        
        start_text = ttk.Label(getting_started, wraplength=650, justify=tk.LEFT, text="""
1. Connect to your router:
   • Enter your router's IP address (typically 192.168.1.1 or 192.168.8.1)
   • Enter your username and password (typically admin/admin)
   • Click the Connect button
   
2. Once connected, the app will:
   • Scan for available 4G and 5G bands
   • Display your current signal information
   • Show which bands you're currently connected to
   
3. The "Auto-connect at startup" option will automatically connect when you open the app
4. The "Run Speedtest on Startup" option will run a speedtest immediately after connecting
5. "Use Huawei LTE API library" enables advanced features (recommended)
        """)
        start_text.pack(padx=15, pady=10, fill=tk.BOTH, expand=True)
        
        # Band Selection tab
        band_selection = ttk.Frame(notebook)
        notebook.add(band_selection, text="Band Selection")
        
        ttk.Label(band_selection, text="Understanding Band Selection", 
                 font=("TkDefaultFont", 12, "bold")).pack(pady=10)
        
        band_text = ttk.Label(band_selection, wraplength=650, justify=tk.LEFT, text="""
The Band Selection section lets you control which frequency bands your router uses:

• 4G Bands tab: Select which 4G/LTE bands to use
• 5G Bands tab: Select which 5G bands to use (if your router supports 5G)

Within each tab:
• The checkboxes show which bands are currently in use (automatically updated)
• You can manually select or deselect bands
• "Select All" and "Clear All" buttons quickly change all bands
• "Apply Selection" sends your chosen bands to the router

Why change bands?
• Different bands offer different coverage, speed, and building penetration
• Lower bands (B8, B20, B28) provide better coverage and building penetration
• Higher bands (B1, B3, B7) provide better speeds in good signal conditions
• Finding the right combination can dramatically improve your connection
        """)
        band_text.pack(padx=15, pady=10, fill=tk.BOTH, expand=True)
        
        # Optimization tab
        optimization = ttk.Frame(notebook)
        notebook.add(optimization, text="Optimization")
        
        ttk.Label(optimization, text="Band Optimization Features", 
                 font=("TkDefaultFont", 12, "bold")).pack(pady=10)
        
        opt_text = ttk.Label(optimization, wraplength=650, justify=tk.LEFT, text="""
The app offers two optimization methods:

1. Basic Optimization (Optimise Bands button):
   • Tests each band individually for signal quality
   • Ranks bands based on RSRP and SINR values
   • Recommends the best bands to use
   • Generates a report with the results
   • Quick but less thorough

2. Enhanced Optimization:
   • Comprehensive testing of all available bands
   • Tests both 4G and 5G bands (if available)
   • Runs speed tests on the best bands
   • Measures signal quality and actual throughput
   • Creates a detailed report with recommendations
   • Takes longer but provides better recommendations

After optimization:
• You can apply the recommended settings with one click
• View the detailed report to understand the results
• Save the configuration for future use
        """)
        opt_text.pack(padx=15, pady=10, fill=tk.BOTH, expand=True)
        
        # Advanced Features tab
        advanced = ttk.Frame(notebook)
        notebook.add(advanced, text="Advanced Features")
        
        ttk.Label(advanced, text="Advanced Features & Troubleshooting", 
                 font=("TkDefaultFont", 12, "bold")).pack(pady=10)
        
        adv_text = ttk.Label(advanced, wraplength=650, justify=tk.LEFT, text="""
Advanced Options:

1. Network Aggregation:
   • Allows separate control of upload and download bands
   • Useful for fine-tuning your connection
   • Apply with "Apply Network Configuration" button

2. Network Mode:
   • Quickly switch between network types (2G/3G/4G/5G)
   • Useful for testing or forcing specific network modes
   • Apply with the "Apply" button next to the dropdown

Troubleshooting:

• If you get connection errors, try disabling "Use Huawei LTE API library"
• If speedtests fail, try running them manually later
• If band selection doesn't work, try disconnecting and reconnecting
• Check the detailed log tab for more information about errors
• Make sure you have the required libraries installed:
  - speedtest-cli (for speed testing)
  - huawei-lte-api (for advanced features)

For best results:
• Place your router near a window or high location
• Try different band combinations based on the optimization results
• Run tests at different times of day to find optimal settings
        """)
        adv_text.pack(padx=15, pady=10, fill=tk.BOTH, expand=True)
        
        # Add OK button at the bottom
        ttk.Button(dialog, text="Close", command=dialog.destroy).pack(pady=10)

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