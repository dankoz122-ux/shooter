@echo off
setlocal
cd /d "%~dp0"
title ZonaKontakta LAN Server
where node.exe >nul 2>&1
if not "%errorlevel%"=="0" goto NODE_MISSING
if exist "node_modules\express\package.json" goto RUN_SERVER
echo Installing server packages. Internet is required for the first run.
call npm.cmd install
if not "%errorlevel%"=="0" goto INSTALL_FAILED
:RUN_SERVER
node server.js
echo.
echo Server stopped. Read any error message above.
pause
exit /b 0
:NODE_MISSING
echo Node.js is missing. Install Node.js LTS from https://nodejs.org/ and retry.
pause
exit /b 1
:INSTALL_FAILED
echo npm install failed. Check internet access and retry.
pause
exit /b 1
