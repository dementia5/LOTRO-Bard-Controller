# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['midi2key_gui - Final.py'],
    pathex=[],
    binaries=[],
    datas=[('bard_background.png', '.'), ('bard w moog.png', '.')],
    hiddenimports=['mido.backends.rtmidi'],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='LOTRO_MIDI_Controller',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=['bard_background.png'],
)
