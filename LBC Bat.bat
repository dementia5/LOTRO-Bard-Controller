@echo off
set "PYTHON_EXE=C:\Python313\python.exe"
set "SCRIPT_PATH=C:\Users\<USER>\Documents\The Lord of the Rings Online\midi2key-main\midi2key_gui - Final.py"

:: Run as administrator using PowerShell
powershell -Command "Start-Process -FilePath '%PYTHON_EXE%' -ArgumentList '\"%SCRIPT_PATH%\"' -WorkingDirectory 'C:\Users\<USER>\Documents\The Lord of the Rings Online\midi2key-main' -Verb RunAs"