@echo off
setlocal
cd /d "%~dp0"
title ZonaKontakta LAN
where node.exe >nul 2>&1
if not "%errorlevel%"=="0" goto NODE_MISSING
if exist "node_modules\express\package.json" goto START_SERVER
echo Installing server packages. Internet is required for the first run.
call npm.cmd install
if not "%errorlevel%"=="0" goto INSTALL_FAILED
:START_SERVER
start "ZonaKontakta Server" /D "%~dp0" cmd /k "node server.js"
echo Waiting for the server to start...
set tries=0
:WAIT_LOOP
set /a tries=%tries%+1 >nul
curl.exe -fsS http://127.0.0.1:3000/health >nul 2>&1
if "%errorlevel%"=="0" goto OPEN_GAME
if "%tries%"=="20" goto SERVER_FAILED
timeout /t 1 /nobreak >nul
goto WAIT_LOOP
:OPEN_GAME
start "" http://localhost:3000
exit /b 0
:NODE_MISSING
echo Node.js is missing. Install Node.js LTS from https://nodejs.org/ and retry.
pause
exit /b 1
:INSTALL_FAILED
echo npm install failed. Check internet access and retry.
pause
exit /b 1
:SERVER_FAILED
echo Server did not start. Read the separate server window for details.
pause
exit /b 1
