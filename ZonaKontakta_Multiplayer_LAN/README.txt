ZonaKontakta LAN Multiplayer

WINDOWS QUICK START
1. Extract this ZIP to a normal folder, for example C:\Games\ZonaKontaktaLAN. Do not run files from inside the ZIP.
2. Install Node.js LTS from https://nodejs.org/ if needed.
3. Double-click START_GAME.bat. On first run it installs npm packages, starts the server in a separate window, then opens the game.
4. Keep the server window open while playing.

JOIN FROM ANOTHER PC ON THE SAME WIFI/LAN
Read the server window. It prints URLs similar to http://192.168.1.15:3000. On the other PC, open the host PC's URL in a browser. Do not use localhost on the other PC.

SERVER ONLY
Double-click START_SERVER.bat.

TROUBLESHOOTING
- Node.js must be installed.
- First run needs internet to download npm packages.
- If Windows Firewall asks, allow Node.js on Private networks.
- This is a LAN prototype and still needs a real two-PC gameplay test.


Spawn points: connected players receive different map waypoint indices, so they start at separate locations instead of stacking at the solo spawn.
