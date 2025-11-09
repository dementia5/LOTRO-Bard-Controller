@echo off
echo Starting LOTRO MIDI Controller GUI with Administrator privileges...
echo Current directory: %cd%
echo Python path: %~dp0

REM Change to the script directory
cd /d "%~dp0"

REM Try to run with full path to avoid issues
powershell -Command "Start-Process python -ArgumentList '\"%~dp0midi2key_gui - Final.py\"' -Verb RunAs -WorkingDirectory '%~dp0'"

REM Alternative method if the above fails
REM powershell -Command "Start-Process cmd -ArgumentList '/k python \"midi2key_gui.py - final\"' -Verb RunAs -WorkingDirectory '%~dp0'"

echo Batch file completed.
pause