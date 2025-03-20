# Huawei Router Band Tool

A powerful tool for optimising band selection to maximise signal quality and internet speeds on Huawei CPE Pro 2 routers.

## Features

- **Band Optimisation:** Automatically tests all available bands and recommends the best combination based on signal quality
- **Enhanced Optimisation:** Combines signal quality metrics with speed tests for the most accurate recommendations
- **Speed Testing:** Built-in speed testing using the speedtest.net API
- **Signal Monitoring:** Real-time monitoring of signal metrics including RSRP, SINR, RSRQ
- **User-friendly Interface:** Clean, intuitive interface with detailed logging views
- **Band Configuration:** Manually select bands or use the optimisation recommendations
- **Reporting:** Generates detailed optimisation reports for future reference

## Installation

1. Make sure you have Python 3.7+ installed
2. Clone this repository:
   ```
   git clone https://github.com/yourusername/huawei-band-optimiser.git
   cd huawei-band-optimiser
   ```
3. Install the required dependencies:
   ```
   pip install -r requirements.txt
   ```

## Usage

Run the application:
```
python main.py
```

### Connecting to your router

1. Enter your router's IP address (default: 192.168.1.1)
2. Enter your username and password
3. Click "Connect"

### Optimising Bands

1. Click "Optimise Bands" to test signal quality on all available bands
2. Review the results in the summary dialogue
3. Click "Apply These Settings" to use the recommended band configuration

### Enhanced Optimisation

1. Click "Enhanced Optimise" to run a comprehensive test that includes speed tests
2. Wait for the tests to complete (this may take several minutes)
3. Review the detailed results and apply if desired

### Speed Testing

Click "Speed Test" to run a standalone speed test using your current band configuration.

## Configuration

The application saves your preferences in a `config.json` file, including:
- Router IP address
- Login credentials
- Auto-connect setting
- Speed test on startup preference

## Troubleshooting

- **API Restrictions:** Some carrier-locked routers may have API restrictions that limit functionality
- **Connection Issues:** Ensure your router is reachable at the specified IP
- **Speed Test Failures:** Check your internet connection or try again later

## Licence

[MIT Licence](LICENCE)

## Support the Project

If you find this tool helpful and would like to support its development, you can make a donation. Your support helps maintain and improve the project!

[![PayPal](https://img.shields.io/badge/Donate-PayPal-blue.svg?logo=paypal&style=for-the-badge)](https://www.paypal.com/ncp/payment/HLVZ82C6FKM2E)

Your support helps:
- Maintain and improve the application
- Add new features and optimisations
- Keep the project up to date with router firmware changes
- Provide better documentation and support

Thank you for your support! 💖

## Acknowledgements

- [speedtest-cli](https://github.com/sivel/speedtest-cli) for speed testing functionality
- [huawei-lte-api](https://github.com/Salamek/huawei-lte-api) for advanced Huawei router API access 