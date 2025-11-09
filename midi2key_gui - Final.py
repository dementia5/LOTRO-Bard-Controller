"""
LOTRO MIDI Controller GUI with Arpeggiator
A graphical interface for the MIDI-to-keyboard mapper with built-in arpeggiator
"""

import tkinter as tk
from tkinter import ttk, messagebox
import threading
import time
import mido
from ctypes import windll, Structure, c_ulong, c_ushort, Union, byref, sizeof, c_uint
import queue
import random
import os
from PIL import Image, ImageTk
import keyboard
import math
import numpy as np
from collections import deque

# Constants from working midi2key.py
KEYEVENTF_UP = 0x0002

class MIDIControllerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("LOTRO MIDI Controller v2.0")
        
        # Position window on left monitor if multiple monitors available
        self.position_on_left_monitor()
        
        self.root.configure(bg='#2b2b2b')
        
        # Register cleanup handler for proper hotkey cleanup
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # Check for Cinzel font availability, fallback to appropriate classical fonts
        self.title_font = self.get_available_font(['Cinzel', 'Trajan Pro', 'Times New Roman', 'Georgia'])
        self.header_font = self.get_available_font(['Cinzel', 'Trajan Pro', 'Times New Roman', 'Georgia'])
        self.button_font = self.get_available_font(['Cinzel', 'Trajan Pro', 'Times New Roman', 'Georgia'])
        
        # MIDI and control variables
        self.midi_port = None
        self.is_running = False
        self.pitch_offset = 0
        self.message_queue = queue.Queue()
        
        # Arpeggiator variables
        self.arp_enabled = tk.BooleanVar()
        self.arp_speed = tk.DoubleVar(value=120)  # BPM
        self.arp_pattern = tk.StringVar(value="Up")
        self.arp_octaves = tk.IntVar(value=1)
        self.arp_notes = []
        self.arp_thread = None
        self.arp_running = False
        
        # LOTRO key mapping based on in-game screenshots - ORIGINAL WORKING VERSION
        self.action_map = {
            # Base octave (B2-C4) from screenshot 1 - ORIGINAL MAPPING
            47: ('ctrl', 0x31), # B2 -> CTRL+1
            48: 0x31, # C3 -> 1
            49: ('ctrl', 0x32), # C#3 -> CTRL+2
            50: 0x32, # D3 -> 2  
            51: ('ctrl', 0x33), # D#3 -> CTRL+3
            52: 0x33, # E3 -> 3
            53: 0x34, # F3 -> 4
            54: ('ctrl', 0x35), # F#3 -> CTRL+5
            55: 0x35, # G3 -> 5
            56: ('ctrl', 0x36), # G#3 -> CTRL+6
            57: 0x36, # A3 -> 6
            58: ('ctrl', 0x37), # A#3 -> CTRL+7
            59: 0x37, # B3 -> 7
            60: 0x38, # C4 -> 8
            
            # Higher octave (C#4-C5) - ORIGINAL WORKING SHIFT+CTRL COMBINATIONS
            61: ('shift+ctrl', 0x31), # C#4 -> SHIFT+CTRL+2
            62: ('shift', 0x32), # D4 -> SHIFT+2
            63: ('shift+ctrl', 0x33), # D#4 -> CTRL+SHIFT+3
            64: ('shift', 0x33), # E4 -> SHIFT+3
            65: ('shift', 0x34), # F4 -> SHIFT+4
            66: ('shift+ctrl', 0x35), # F#4 -> SHIFT+CTRL+5
            67: ('shift', 0x35), # G4 -> SHIFT+5
            68: ('shift+ctrl', 0x36), # G#4 -> SHIFT+CTRL+6
            69: ('shift', 0x36), # A4 -> SHIFT+6
            70: ('shift+ctrl', 0x37), # A#4 -> SHIFT+CTRL+7
            71: ('shift', 0x37), # B4 -> SHIFT+7
            72: ('shift', 0x38), # C5 -> SHIFT+8
            
            # Extended range (C#5-C6) - Using ALT to avoid CTRL conflicts
            # 73: ('shift+ctrl', 0x38), # C#5 -> SHIFT+CTRL+8
            # 74: 0x31, # D5 -> 1 (cycle back to base keys)
            # 75: ('alt', 0x31), # D#5 -> ALT+1 (safer than CTRL)
            # 76: 0x32, # E5 -> 2 
            # 77: ('alt', 0x32), # F5 -> ALT+2 (safer than CTRL)
            # 78: 0x33, # F#5 -> 3
            # 79: ('alt', 0x33), # G5 -> ALT+3 (safer than CTRL)
            # 80: 0x34, # G#5 -> 4
            # 81: ('alt', 0x34), # A5 -> ALT+4 (safer than CTRL)
            # 82: 0x35, # A#5 -> 5
            # 83: ('alt', 0x35), # B5 -> ALT+5 (safer than CTRL)
            # 84: 0x36, # C6 -> 6
            
            # # Even higher range (C#6-C7)
            # 85: ('ctrl', 0x36), # C#6 -> CTRL+6
            # 86: 0x37, # D6 -> 7
            # 87: ('ctrl', 0x37), # D#6 -> CTRL+7
            # 88: 0x38, # E6 -> 8
            # 89: ('ctrl', 0x38), # F6 -> CTRL+8
            # 90: ('shift', 0x31), # F#6 -> SHIFT+1
            # 91: ('shift+ctrl', 0x31), # G6 -> SHIFT+CTRL+1
            # 92: ('shift', 0x32), # G#6 -> SHIFT+2
            # 93: ('shift+ctrl', 0x32), # A6 -> SHIFT+CTRL+2
            # 94: ('shift', 0x33), # A#6 -> SHIFT+3
            # 95: ('shift+ctrl', 0x33), # B6 -> SHIFT+CTRL+3
            # 96: ('shift', 0x34), # C7 -> SHIFT+4

        }
        
        # Chord triggering system - controlled by GUI checkboxes
        self.chord_modifiers = {
            'major': 'major',
            'minor': 'minor',  
            'sus2': 'sus2',
            'sus4': 'sus4',
            'dim': 'dim',
            'aug': 'aug',
            'maj7': 'maj7',
            'min7': 'min7'
        }
        
        # Chord intervals (semitones from root)
        self.chord_patterns = {
            'major': [0, 4, 7],           # Root, Major 3rd, Perfect 5th
            'minor': [0, 3, 7],           # Root, Minor 3rd, Perfect 5th
            'sus2': [0, 2, 7],            # Root, Major 2nd, Perfect 5th
            'sus4': [0, 5, 7],            # Root, Perfect 4th, Perfect 5th
            'dim': [0, 3, 6],             # Root, Minor 3rd, Tritone
            'aug': [0, 4, 8],             # Root, Major 3rd, Augmented 5th
            'maj7': [0, 4, 7, 11],        # Root, Major 3rd, Perfect 5th, Major 7th
            'min7': [0, 3, 7, 10],        # Root, Minor 3rd, Perfect 5th, Minor 7th
        }
        

        self.last_chord_notes = []  # Track last played chord notes for proper release
        
        # Chord system
        self.chord_types = ['None', 'Major', 'Minor', 'Sus2', 'Sus4', 'Diminished', 'Augmented', 'Major 7th', 'Minor 7th']
        self.chord_type_map = {
            'None': None,
            'Major': 'major',
            'Minor': 'minor', 
            'Sus2': 'sus2',
            'Sus4': 'sus4',
            'Diminished': 'dim',
            'Augmented': 'aug',
            'Major 7th': 'maj7',
            'Minor 7th': 'min7'
        }
        self.chord_combobox = None
        self.current_chord_type = 'None'
        
        # ABC notation variables
        self.abc_notes = []
        self.abc_start_time = None
        self.abc_tempo = 120  # Default BPM
        
        # File tracking variables for title updates
        self.current_abc_filename = None
        self.current_midi_filename = None
        
        # Spectrum analyzer variables
        self.spectrum_data = deque(maxlen=88)  # 88 piano keys
        self.spectrum_canvas = None
        self.spectrum_update_thread = None
        self.spectrum_running = False
        
        # Initialize spectrum data (MIDI notes 21-108, full piano range)
        for i in range(88):
            self.spectrum_data.append(0.0)
        
        self.setup_gui()
        self.setup_midi_ports()
        
        # Set up proper window close handling
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
    
    def position_on_left_monitor(self):
        """Position the window on the left monitor if multiple monitors are available"""
        try:
            # Set default size
            window_width = 1840
            window_height = 1280
            
            # Try to get monitor information using Windows API
            try:
                from ctypes import windll, byref, WINFUNCTYPE, POINTER
                from ctypes.wintypes import BOOL, HMONITOR, HDC, RECT, LPARAM
                
                monitors = []
                
                def monitor_enum_proc(hmonitor, hdc, lprect, lparam):
                    monitors.append({
                        'handle': hmonitor,
                        'left': lprect.contents.left,
                        'top': lprect.contents.top,
                        'right': lprect.contents.right,
                        'bottom': lprect.contents.bottom,
                        'width': lprect.contents.right - lprect.contents.left,
                        'height': lprect.contents.bottom - lprect.contents.top
                    })
                    return True
                
                MonitorEnumProc = WINFUNCTYPE(BOOL, HMONITOR, HDC, POINTER(RECT), LPARAM)
                windll.user32.EnumDisplayMonitors(None, None, MonitorEnumProc(monitor_enum_proc), 0)
                
                if len(monitors) > 1:
                    # Multiple monitors detected - position on left monitor and maximize
                    left_monitor = min(monitors, key=lambda m: m['left'])
                    
                    # Position on left monitor first
                    x_position = left_monitor['left']
                    y_position = left_monitor['top']
                    self.root.geometry(f"+{x_position}+{y_position}")
                    
                    # Then maximize on that monitor
                    self.root.state('zoomed')
                    print(f"🖥️ LBC maximized on left monitor ({left_monitor['width']}x{left_monitor['height']})")
                    return
                elif len(monitors) == 1:
                    # Single monitor detected via API - maximize it
                    self.root.state('zoomed')
                    print(f"🖥️ LBC maximized on single monitor ({monitors[0]['width']}x{monitors[0]['height']})")
                    return
                    
            except Exception as api_error:
                print(f"Windows API monitor detection failed: {api_error}")
            
            # Fallback: Basic multi-monitor detection
            screen_width = self.root.winfo_screenwidth()
            screen_height = self.root.winfo_screenheight()
            
            if screen_width > 1920:
                # Likely multiple monitors - position on left side and maximize
                self.root.geometry("+0+0")  # Position at left edge first
                self.root.state('zoomed')   # Then maximize
                print("🖥️ LBC maximized on left side (estimated)")
            else:
                # Single monitor - maximize for best experience
                self.root.state('zoomed')  # Windows equivalent of maximize
                print("🖥️ LBC maximized on single monitor")
                
        except Exception as e:
            # Ultimate fallback - still maximize
            self.root.state('zoomed')
            print(f"Monitor positioning failed, maximizing anyway: {e}")
        
    def on_closing(self):
        """Handle window close event - properly shut down all threads"""
        try:
            self.log_status("🔄 Shutting down application...")
            
            # Stop all MIDI processing
            self.is_running = False
            self.arp_running = False
            
            # Stop spectrum analyzer
            self.stop_spectrum_analyzer()
            
            # Stop all playback
            if hasattr(self, 'midi_playing') and self.midi_playing:
                self.stop_midi_playback()
            
            if hasattr(self, 'abc_playing') and self.abc_playing:
                self.stop_abc_playback()
            
            # Close MIDI port
            if self.midi_port:
                try:
                    self.midi_port.close()
                except:
                    pass
                self.midi_port = None
            
            # Stop pygame mixer if it's running
            try:
                import pygame
                if pygame.mixer.get_init():
                    pygame.mixer.quit()
            except:
                pass
            
            # Give threads time to clean up
            time.sleep(0.1)
            
            self.log_status("✓ Application shutdown complete")
            
        except Exception as e:
            print(f"Error during shutdown: {e}")
        finally:
            # Force destroy the window
            self.root.quit()
            self.root.destroy()
    
    def get_available_font(self, font_list):
        """Check which fonts are available and return the first available one"""
        import tkinter.font as tkFont
        available_fonts = tkFont.families()
        
        for font_name in font_list:
            if font_name in available_fonts:
                return font_name
        
        # Fallback to default if none found
        return 'TkDefaultFont'
    
    def update_abc_title(self, filename=None):
        """Update the ABC section title with filename"""
        if filename:
            short_name = os.path.basename(filename)
            self.abc_frame.config(text=f"📝 ABC NOTATION EXPORT - {short_name}")
            self.current_abc_filename = filename
        else:
            self.abc_frame.config(text="📝 ABC NOTATION EXPORT")
            self.current_abc_filename = None
    
    def update_midi_title(self, filename=None):
        """Update the MIDI section title with filename"""
        if filename:
            short_name = os.path.basename(filename)
            self.midi_frame.config(text=f"🎵 MIDI FILE PLAYBACK - {short_name}")
            self.current_midi_filename = filename
        else:
            self.midi_frame.config(text="🎵 MIDI FILE PLAYBACK")
            self.current_midi_filename = None
        
    def setup_gui(self):
        """Create the single-page GUI layout with transparent background"""
        # Set main window background to a nice LOTRO-themed color
        self.root.configure(bg='#1a1a1a')
        
        # Main container frame
        self.main_frame = tk.Frame(self.root, bg='#1a1a1a', relief='raised', bd=2)
        self.main_frame.pack(fill='both', expand=True, padx=20, pady=20)
        
        # Title section
        title_frame = tk.Frame(self.main_frame, bg='#1a1a1a')
        title_frame.pack(pady=10)
        
        title_label = tk.Label(title_frame, text="🎵 LOTRO Bard Controller 🎸", 
                              font=(self.title_font, 28, 'bold'), fg='#DAA520', bg='#1a1a1a',
                              relief='raised', bd=2, padx=10, pady=5)
        title_label.pack()
        
        subtitle_label = tk.Label(title_frame, text="Transform your MIDI keyboard into a LOTRO instrument", 
                                 font=(self.title_font, 14, 'italic'), fg='#F5DEB3', bg='#1a1a1a')
        subtitle_label.pack(pady=5)
        
        # Disclaimer
        disclaimer_label = tk.Label(title_frame, text="⚠️ DISCLAIMER: Unofficial tool - Use at your own risk. Check LOTRO ToS. Not affiliated with Standing Stone Games.", 
                                   font=('Arial', 9, 'italic'), fg='#CD853F', bg='#1a1a1a', wraplength=800)
        disclaimer_label.pack(pady=(0, 10))
        
        # Create tabbed interface with custom styling
        style = ttk.Style()
        style.configure('Custom.TNotebook', tabposition='n')
        style.configure('Custom.TNotebook.Tab', 
                       padding=[20, 10],
                       font=('Georgia', 12, 'bold'),
                       foreground='#DAA520',
                       background='#2a2a2a',
                       focuscolor='none')
        style.map('Custom.TNotebook.Tab',
                 background=[('selected', '#4a4a4a'), ('active', '#3a3a3a')])
        
        self.notebook = ttk.Notebook(self.main_frame, style='Custom.TNotebook')
        self.notebook.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Main Control Tab (keep existing layout)
        main_tab = tk.Frame(self.notebook, bg='#1a1a1a')
        self.notebook.add(main_tab, text='   🎹 MAIN CONTROL   ')
        
        # Create main content area with three columns in main tab
        content_frame = tk.Frame(main_tab, bg='#1a1a1a')
        content_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Left column - MIDI Control
        left_frame = tk.Frame(content_frame, bg='#2a2a2a', relief='sunken', bd=2)
        left_frame.pack(side='left', fill='both', expand=True, padx=5)
        self.setup_midi_section(left_frame)
        
        # Middle column - Arpeggiator
        middle_frame = tk.Frame(content_frame, bg='#2a2a2a', relief='sunken', bd=2)
        middle_frame.pack(side='left', fill='both', expand=True, padx=5)
        self.setup_arpeggiator_section(middle_frame)
        
        # Right column - Key Mapping & Status
        right_frame = tk.Frame(content_frame, bg='#2a2a2a', relief='sunken', bd=2)
        right_frame.pack(side='left', fill='both', expand=True, padx=5)
        self.setup_mapping_and_status_section(right_frame)
        
        # Key Mappings Tab
        mapping_tab = tk.Frame(self.notebook, bg='#1a1a1a')
        self.notebook.add(mapping_tab, text='   🎸 KEY MAPPINGS & INSTRUMENTS   ')
        self.setup_key_mappings_tab(mapping_tab)
        
        # Initialize note status display
        self.initialize_note_status_display()
        
        # Setup global hotkey for chord cycling (CTRL + `)
        self.setup_global_hotkey()

    def setup_global_hotkey(self):
        """Setup global hotkey that works even when app is not in focus"""
        try:
            keyboard.add_hotkey('ctrl+`', self.cycle_chord_type_global)
            print("Global hotkey CTRL+` registered successfully")
        except Exception as e:
            print(f"Failed to register global hotkey: {e}")
            messagebox.showwarning("Hotkey Warning", 
                                 f"Could not register global hotkey CTRL+`.\n"
                                 f"You may need to run as administrator.\n"
                                 f"Error: {e}")

    def cycle_chord_type_global(self):
        """Global hotkey handler - cycles chords OR arp patterns based on active tab"""
        # Schedule the UI update on the main thread
        self.root.after(0, self.cycle_active_setting)

    def cycle_chord_type(self, event=None):
        """Cycle through chord types using CTRL+` hotkey"""
        if self.chord_combobox:
            # Get current index
            current_index = self.chord_combobox.current()
            # Cycle to next chord type
            next_index = (current_index + 1) % len(self.chord_types)
            # Update combobox selection
            self.chord_combobox.current(next_index)
            # Trigger the selection event
            self.on_chord_selection_changed()
            
            # Show notification in title bar temporarily
            chord_name = self.chord_types[next_index]
            original_title = self.root.title()
            self.root.title(f"LOTRO MIDI Controller - {chord_name}")
            self.root.after(2000, lambda: self.root.title(original_title))  # Reset after 2 seconds
    
    def cycle_active_setting(self):
        """Cycle through chord types or arp patterns based on active tab and arp state"""
        try:
            # Get the currently selected tab
            current_tab = self.notebook.index(self.notebook.select())
            
            if current_tab == 0:  # Main tab - check if arpeggiator is enabled
                if self.arp_enabled.get():
                    self.cycle_arp_pattern()
                else:
                    self.cycle_chord_type()
            elif current_tab == 1:  # Key mappings tab - always do chord cycling 
                self.cycle_chord_type()
            else:
                # Default to chord cycling for other tabs
                self.cycle_chord_type()
                
        except Exception as e:
            # Fallback to chord cycling if anything goes wrong
            self.cycle_chord_type()
    
    def cycle_arp_pattern(self):
        """Cycle through arpeggiator patterns using CTRL+` hotkey"""
        # Get list of patterns from the combobox
        patterns = ["Up", "Down", "Up-Down", "Random", "As Played", 
                   "Pentatonic", "Diatonic", "Chromatic", "Mixolydian", 
                   "Dorian", "Lydian", "Blues Scale"]
        
        # Get current pattern
        current_pattern = self.arp_pattern.get()
        
        # Find current index
        try:
            current_index = patterns.index(current_pattern)
        except ValueError:
            current_index = 0  # Default to first pattern if not found
        
        # Cycle to next pattern
        next_index = (current_index + 1) % len(patterns)
        next_pattern = patterns[next_index]
        
        # Update the pattern
        self.arp_pattern.set(next_pattern)
        
        # Show notification in title bar temporarily  
        original_title = self.root.title()
        self.root.title(f"LOTRO MIDI Controller - Arp: {next_pattern}")
        self.root.after(2000, lambda: self.root.title(original_title))  # Reset after 2 seconds
        
        # Log the change
        self.log_status(f"🎶 Arp Pattern: {next_pattern}")

    def on_chord_selection_changed(self):
        """Handle chord selection change from combobox"""
        if self.chord_combobox:
            selected = self.chord_combobox.get()
            self.current_chord_type = selected
            
            # Update status
            if selected == 'None':
                self.log_status("🎵 Chord type: Single Note Mode")
            else:
                self.log_status(f"🎶 Chord type: {selected} chords activated")
            
            # Update displays
            self.update_chord_status_display()
            self.update_chord_status_gui()
    
    def on_closing(self):
        """Clean up resources when closing the application"""
        try:
            # Unhook global hotkeys
            keyboard.unhook_all()
            print("Global hotkeys cleaned up")
        except Exception as e:
            print(f"Error during cleanup: {e}")
        
        # Close the application
        self.root.destroy()
    
    def scroll_control_combobox(self, direction):
        """Scroll ARP pattern or chord combobox up/down based on active tab"""
        current_tab = self.notebook.index(self.notebook.select())
        if current_tab == 0:  # Main tab: ARP pattern
            patterns = ["Up", "Down", "Up-Down", "Random", "As Played", 
                        "Pentatonic", "Diatonic", "Chromatic", "Mixolydian", 
                        "Dorian", "Lydian", "Blues Scale"]
            current_pattern = self.arp_pattern.get()
            idx = patterns.index(current_pattern) if current_pattern in patterns else 0
            new_idx = (idx + direction) % len(patterns)
            self.arp_pattern.set(patterns[new_idx])
            self.log_status(f"🎶 ARP pattern changed to: {patterns[new_idx]}")
        elif current_tab == 1:  # Key mappings tab: Chord combobox
            if self.chord_combobox:
                idx = self.chord_combobox.current()
                new_idx = (idx + direction) % len(self.chord_types)
                self.chord_combobox.current(new_idx)
                self.on_chord_selection_changed()
                self.log_status(f"🎶 Chord type changed to: {self.chord_types[new_idx]}")
    
    def update_chord_status_gui(self):
        """Update the GUI chord status display"""
        if hasattr(self, 'chord_status_label_gui'):
            if self.current_chord_type == 'None':
                self.chord_status_label_gui.config(
                    text="No chords selected - Single note mode",
                    fg='#F5DEB3'
                )
            else:
                chord_descriptions = {
                    'Major': 'Major (1-3-5)',
                    'Minor': 'Minor (1-♭3-5)', 
                    'Sus2': 'Sus2 (1-2-5)',
                    'Sus4': 'Sus4 (1-4-5)',
                    'Diminished': 'Diminished (1-♭3-♭5)',
                    'Augmented': 'Augmented (1-3-#5)',
                    'Major 7th': 'Major 7th (1-3-5-7)',
                    'Minor 7th': 'Minor 7th (1-♭3-5-♭7)'
                }
                description = chord_descriptions.get(self.current_chord_type, self.current_chord_type)
                self.chord_status_label_gui.config(
                    text=f"🎶 CHORD MODE ACTIVE: {description.upper()}",
                    fg='#32CD32'
                )
    
    def update_chord_status_display(self):
        """Update the chord status display with active chord type"""
        if not hasattr(self, 'chord_status_label'):
            return
            
        if self.current_chord_type == 'None':
            self.chord_status_label.config(
                text="No chord modifiers active\n",
                fg='#F5DEB3'
            )
        else:
            self.chord_status_label.config(
                text=f"🎶 CHORD MODE ACTIVE 🎶\n{self.current_chord_type} chords",
                fg='#32CD32'
            )
    
    def get_chord_notes(self, root_note, chord_type):
        """Calculate the notes for a chord based on root note and chord type"""
        if chord_type not in self.chord_patterns:
            return [root_note]
        
        intervals = self.chord_patterns[chord_type]
        
        # Use standard Major 7th pattern for all keys
        # We'll handle SHIFT+CTRL issues in the action_map instead
        if chord_type == 'maj7':
            intervals = [0, 4, 7, 11]
        
        chord_notes = []
        for interval in intervals:
            chord_note = root_note + interval
            # Keep notes within MIDI range (21-108 for 88-key piano)
            if 21 <= chord_note <= 108:
                chord_notes.append(chord_note)
        
        return chord_notes
    
    def play_chord(self, root_note):
        """Play a chord based on current chord type and root note"""
       # Release all notes from previous chord before updating last_chord_notes
        if hasattr(self, 'last_chord_notes') and self.last_chord_notes:
            for prev_note in self.last_chord_notes:
                prev_key_mapping = self.action_map.get(prev_note)
                if prev_key_mapping:
                    self.send_note_key(prev_note, prev_key_mapping, press=False)
                    self.update_note_spectrum(prev_note, 0, False)

        if self.current_chord_type == 'None':
            # No chord type selected, play single note
            self.last_chord_notes = [root_note]
            return [root_note]

        # Get the chord type key from the type mapping
        chord_type_key = self.chord_type_map.get(self.current_chord_type)
        if chord_type_key:
            chord_notes = self.get_chord_notes(root_note, chord_type_key)
            
            # Remember the chord notes for proper release
            self.last_chord_notes = chord_notes.copy()
            
            # Update spectrum display for chord notes
            for chord_note in chord_notes:
                self.update_note_spectrum(chord_note, 100, True)  # Use velocity 100 for chord notes
            
            self.log_status(f"Playing {self.current_chord_type} chord: {chord_notes}")
            return chord_notes
        else:
            # Fallback to single note if chord type not found
            self.last_chord_notes = [root_note]
            return [root_note]
    
    def setup_midi_section(self, parent):
        """Setup the MIDI control section"""
        # Section title
        title_label = tk.Label(parent, text="🎹 MIDI Control", 
                              font=('Cinzel', 16, 'bold'), fg='#DAA520', bg='#2a2a2a')
        title_label.pack(pady=10)
        
        # MIDI Port Selection
        port_frame = tk.LabelFrame(parent, text="🎛️ Select MIDI Port", 
                                  bg='#2a2a2a', fg='#F5DEB3', font=('Cinzel', 11, 'bold'))
        port_frame.pack(fill='x', padx=10, pady=5)
        
        self.port_var = tk.StringVar()
        self.port_dropdown = ttk.Combobox(port_frame, textvariable=self.port_var, 
                                         state="readonly", width=25)
        self.port_dropdown.pack(pady=10)
        
        refresh_btn = tk.Button(port_frame, text="🔄 Refresh Ports", command=self.setup_midi_ports,
                               bg='#8B4513', fg='white', font=('Cinzel', 10, 'bold'),
                               relief='raised', bd=2)
        refresh_btn.pack(pady=5)
        
        # Control Buttons
        control_frame = tk.Frame(parent, bg='#2a2a2a')
        control_frame.pack(pady=15)
        
        self.start_btn = tk.Button(control_frame, text="⚡ Start Playing", 
                                  command=self.start_midi, bg='#228B22', fg='white',
                                  font=('Cinzel', 12, 'bold'), width=15, height=2,
                                  relief='raised', bd=3)
        self.start_btn.pack(pady=5)
        
        self.stop_btn = tk.Button(control_frame, text="🛑 Stop Music", 
                                 command=self.stop_midi, bg='#B22222', fg='white',
                                 font=('Cinzel', 12, 'bold'), width=15, height=2, 
                                 state='disabled', relief='raised', bd=3)
        self.stop_btn.pack(pady=5)

        # Background Image Inset - positioned higher up
        try:
            from PIL import Image, ImageTk
            import os
            image_path = os.path.join(os.path.dirname(__file__), "bard_background.png")
            if os.path.exists(image_path):
                # Load and resize image to fit as an inset
                pil_image = Image.open(image_path)
                # Resize to fit nicely in the left column
                inset_width, inset_height = 400, 600
                pil_image = pil_image.resize((inset_width, inset_height), Image.Resampling.LANCZOS)
                # Create PhotoImage
                self.background_photo = ImageTk.PhotoImage(pil_image)
                # Create image label with border - moved up with less bottom padding
                image_frame = tk.Frame(parent, bg='#8B4513', relief='sunken', bd=3)
                image_frame.pack(pady=(5, 0), padx=10)  # Less top padding, no bottom padding
                image_label = tk.Label(image_frame, image=self.background_photo, 
                                     bg='#8B4513', relief='flat')
                image_label.image = self.background_photo  # Keep a reference!
                image_label.pack(padx=2, pady=2)
                caption_label = tk.Label(parent, text="🏰 Middle-earth Awaits", bg='#2a2a2a', fg='#DAA520', font=('Georgia', 10, 'italic'))
                caption_label.pack(pady=(2, 5))
            else:
                placeholder_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=3, height=150, width=200)
                placeholder_frame.pack(pady=(5, 0), padx=10)
                placeholder_frame.pack_propagate(False)
                placeholder_label = tk.Label(placeholder_frame, text="🏰\nBard Image\nPlaceholder", bg='#1a1a1a', fg='#DAA520', font=('Georgia', 12), justify='center')
                placeholder_label.pack(expand=True)
        except ImportError:
            placeholder_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=3, height=150, width=200)
            placeholder_frame.pack(pady=(5, 0), padx=10)
            placeholder_frame.pack_propagate(False)
            placeholder_label = tk.Label(placeholder_frame, text="🏰\nBard Image\n(PIL Required)", bg='#1a1a1a', fg='#DAA520', font=('Georgia', 12), justify='center')
            placeholder_label.pack(expand=True)

    #     Toggle Music Mode button
    #     self.music_mode_active = False
    #     self.music_mode_btn = tk.Button(control_frame, text="🎼 Enter Music Mode", command=self.toggle_music_mode,
    #                                     bg='#4169E1', fg='white', font=('Cinzel', 12, 'bold'),
    #                                     relief='raised', bd=3, width=15, height=2)
    #     self.music_mode_btn.pack(pady=5)
    
    # def toggle_music_mode(self):
    #     """Toggle LOTRO music mode by sending CTRL+M and update button label."""
    #     try:
    #         import keyboard
    #         keyboard.send('ctrl+m')
    #         self.music_mode_active = not self.music_mode_active
    #         if self.music_mode_active:
    #             self.music_mode_btn.config(text="🎼 Exit Music Mode")
    #         else:
    #             self.music_mode_btn.config(text="🎼 Enter Music Mode")
    #     except Exception as e:
    #         from tkinter import messagebox
    #         messagebox.showerror("Music Mode Error", f"Failed to toggle music mode: {e}")
        
    #     # Background Image Inset - positioned higher up
    #     try:
    #         from PIL import Image, ImageTk
    #         import os
            
    #         image_path = os.path.join(os.path.dirname(__file__), "bard_background.png")
    #         if os.path.exists(image_path):
    #             # Load and resize image to fit as an inset
    #             pil_image = Image.open(image_path)
    #             # Resize to fit nicely in the left column
    #             inset_width, inset_height = 400, 600
    #             pil_image = pil_image.resize((inset_width, inset_height), Image.Resampling.LANCZOS)
                
    #             # Create PhotoImage
    #             self.background_photo = ImageTk.PhotoImage(pil_image)
                
    #             # Create image label with border - moved up with less bottom padding
    #             image_frame = tk.Frame(parent, bg='#8B4513', relief='sunken', bd=3)
    #             image_frame.pack(pady=(5, 0), padx=10)  # Less top padding, no bottom padding
                
    #             image_label = tk.Label(image_frame, image=self.background_photo, 
    #                                  bg='#8B4513', relief='flat')
    #             image_label.image = self.background_photo  # Keep a reference!
    #             image_label.pack(padx=2, pady=2)
    #             caption_label = tk.Label(parent, text="🏰 Middle-earth Awaits", bg='#2a2a2a', fg='#DAA520', font=('Georgia', 10, 'italic'))
    #             caption_label.pack(pady=(2, 5))
    #         else:
    #             placeholder_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=3, height=150, width=200)
    #             placeholder_frame.pack(pady=(5, 0), padx=10)
    #             placeholder_frame.pack_propagate(False)
    #             placeholder_label = tk.Label(placeholder_frame, text="🏰\nBard Image\nPlaceholder", bg='#1a1a1a', fg='#DAA520', font=('Georgia', 12), justify='center')
    #             placeholder_label.pack(expand=True)
    #     except ImportError:
    #         placeholder_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=3, height=150, width=200)
    #         placeholder_frame.pack(pady=(5, 0), padx=10)
    #         placeholder_frame.pack_propagate(False)
    #         placeholder_label = tk.Label(placeholder_frame, text="🏰\nBard Image\n(PIL Required)", bg='#1a1a1a', fg='#DAA520', font=('Georgia', 12), justify='center')
    #         placeholder_label.pack(expand=True)
                
    #             # Add image caption
    #         caption_label = tk.Label(parent, text="🏰 Middle-earth Awaits", 
    #                                    bg='#2a2a2a', fg='#DAA520',
    #                                    font=('Georgia', 10, 'italic'))
    #         caption_label.pack(pady=(2, 5))  # Minimal top padding, small bottom
    #         else:
    #             # Fallback if image doesn't exist
    #             placeholder_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=3, height=150, width=200)
    #             placeholder_frame.pack(pady=(5, 0), padx=10)
    #             placeholder_frame.pack_propagate(False)
                
    #             placeholder_label = tk.Label(placeholder_frame, text="🏰\nBard Image\nPlaceholder", 
    #                                        bg='#1a1a1a', fg='#DAA520',
    #                                        font=('Georgia', 12), justify='center')
    #             placeholder_label.pack(expand=True)
                
    #     except ImportError:
    #         # PIL not available, create simple placeholder
    #         placeholder_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=3, height=150, width=200)
    #         placeholder_frame.pack(pady=(5, 0), padx=10)
    #         placeholder_frame.pack_propagate(False)
            
    #         placeholder_label = tk.Label(placeholder_frame, text="🏰\nBard Image\n(PIL Required)", 
    #                                    bg='#1a1a1a', fg='#DAA520',
    #                                    font=('Georgia', 12), justify='center')
    #         placeholder_label.pack(expand=True)
        

        
    def setup_arpeggiator_section(self, parent):
        """Setup the arpeggiator section"""
        # Section title
        title_label = tk.Label(parent, text="🎼 Arpeggiator", 
                              font=('Cinzel', 16, 'bold'), fg='#DAA520', bg='#2a2a2a')
        title_label.pack(pady=10)
        
        # Arpeggiator Enable
        arp_check = tk.Checkbutton(parent, text="🎵 Enable Auto-Play", 
                                  variable=self.arp_enabled, bg='#2a2a2a', fg='#F5DEB3',
                                  font=('Cinzel', 12, 'bold'), selectcolor='#8B4513',
                                  command=self.toggle_arpeggiator, relief='raised', bd=2)
        arp_check.pack(pady=10)
        
        # Arpeggiator Controls
        controls_frame = tk.LabelFrame(parent, text="Arpeggiator Settings", 
                                     bg='#2a2a2a', fg='#F5DEB3', font=('Cinzel', 11, 'bold'))
        controls_frame.pack(fill='x', padx=10, pady=10)
        
        # Speed control
        tk.Label(controls_frame, text="🕐 Speed (BPM):", bg='#2a2a2a', fg='#F5DEB3',
                font=('Georgia', 10)).pack(pady=2)
        
        speed_scale = tk.Scale(controls_frame, from_=60, to=200, orient='horizontal',
                              variable=self.arp_speed, bg='#2a2a2a', fg='#F5DEB3',
                              highlightbackground='#2a2a2a', length=150,
                              troughcolor='#8B4513')
        speed_scale.pack(pady=5)
        
        # Pattern and Octave controls on same row to save space
        pattern_octave_frame = tk.Frame(controls_frame, bg='#2a2a2a')
        pattern_octave_frame.pack(fill='x', pady=5)
        
        # Pattern selection (left side)
        pattern_frame = tk.Frame(pattern_octave_frame, bg='#2a2a2a')
        pattern_frame.pack(side='left', expand=True, fill='x', padx=5)
        
        tk.Label(pattern_frame, text="🎶 Pattern:", bg='#2a2a2a', fg='#F5DEB3',
                font=('Georgia', 9)).pack()
        
        patterns = ["Up", "Down", "Up-Down", "Random", "As Played", 
                   "Pentatonic", "Diatonic", "Chromatic", "Mixolydian", 
                   "Dorian", "Lydian", "Blues Scale"]
        pattern_dropdown = ttk.Combobox(pattern_frame, textvariable=self.arp_pattern,
                                       values=patterns, state="readonly", width=12)
        pattern_dropdown.pack()
        
        # Hotkey hint for pattern cycling
        tk.Label(pattern_frame, text="(CTRL+` cycles patterns)", 
                font=('Arial', 8, 'italic'), fg='#32CD32', bg='#2a2a2a').pack(pady=(2,0))
        
        # Octave range (right side)
        octave_frame = tk.Frame(pattern_octave_frame, bg='#2a2a2a')
        octave_frame.pack(side='right', expand=True, fill='x', padx=5)
        
        tk.Label(octave_frame, text="🎹 Octaves:", bg='#2a2a2a', fg='#F5DEB3',
                font=('Georgia', 9)).pack()
        
        octave_scale = tk.Scale(octave_frame, from_=1, to=3, orient='horizontal',
                               variable=self.arp_octaves, bg='#2a2a2a', fg='#F5DEB3',
                               highlightbackground='#2a2a2a', length=80,
                               troughcolor='#8B4513')
        octave_scale.pack()
        
        # Note Status display - shows chords in arp mode, raw MIDI in normal mode
        note_frame = tk.LabelFrame(parent, text="🎵 Note Status", 
                                   bg='#2a2a2a', fg='#F5DEB3', font=('Georgia', 11, 'bold'))
        note_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        self.chord_display = tk.Text(note_frame, bg='#1a1a1a', fg='#DAA520', 
                                    font=('Courier', 10), state='disabled', height=25,
                                    relief='sunken', bd=2)
        self.chord_display.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Countdown Display - positioned below Note Status as separate prominent element
        self.countdown_label = tk.Label(parent, text="", 
                                       bg='#2a2a2a', fg='#FFD700',
                                       font=('Georgia', 16, 'bold'), relief='raised', bd=2)
        self.countdown_label.pack(pady=10, padx=10, fill='x')
        
    def setup_mapping_and_status_section(self, parent):
        """Setup the key mapping and status section"""
        # Section title
        title_label = tk.Label(parent, text="🗝️ Key Mapping & Status", 
                              font=('Cinzel', 16, 'bold'), fg='#DAA520', bg='#2a2a2a')
        title_label.pack(pady=10)
        

        # Key Mapping Display - horizontal layout
        mapping_frame = tk.LabelFrame(parent, text="🎹 MIDI to Key Mapping", 
                                     bg='#2a2a2a', fg='#F5DEB3', font=('Cinzel', 11, 'bold'))
        mapping_frame.pack(fill='both', expand=True, padx=10, pady=5)

        # Horizontal container for mapping and tips
        mapping_container = tk.Frame(mapping_frame, bg='#2a2a2a')
        mapping_container.pack(fill='x', expand=True, padx=10, pady=5)

        # Left: MIDI Note → LOTRO Key list
        mapping_text = """🎹 MIDI Note → 🎮 LOTRO Key\n\nC3 (48) → 1 Key    D3 (50) → 2 Key  \nE3 (52) → 3 Key    F3 (53) → 4 Key\nG3 (55) → 5 Key    A3 (57) → 6 Key\nB3 (59) → 7 Key    C4 (60) → 8 Key"""
        mapping_label = tk.Label(mapping_container, text=mapping_text, bg='#2a2a2a', fg='#F5DEB3',
                                font=('Courier', 9), justify='left')
        mapping_label.pack(side='left', anchor='n', padx=(0, 30))

        # Right: Bard's Tips and bullets
        tips_frame = tk.Frame(mapping_container, bg='#2a2a2a')
        tips_frame.pack(side='left', anchor='n')
        tips_title = tk.Label(tips_frame, text="💡 Bard's Tips:", bg='#2a2a2a', fg='#DAA520', font=('Georgia', 10, 'bold'), justify='left')
        tips_title.pack(anchor='w')
        tips_list = [
            "Enter music mode in LOTRO",
            "Equip your instrument",
            "Run as Administrator",
            "Keys 1-8 for melodies, black keys for sharps"
        ]
        for tip in tips_list:
            tip_label = tk.Label(tips_frame, text=f"• {tip}", bg='#2a2a2a', fg='#F5DEB3', font=('Georgia', 9), justify='left')
            tip_label.pack(anchor='w', padx=(10,0))
        
        # Status Frame
        status_frame = tk.LabelFrame(parent, text="📋 Status Log", 
                                   bg='#2a2a2a', fg='#F5DEB3', font=('Georgia', 11, 'bold'))
        status_frame.pack(fill='both', expand=True, padx=10, pady=5)
        
        # Status text widget
        self.status_text = tk.Text(status_frame, bg='#1a1a1a', fg='#FFB347',
                                  font=('Courier', 8), state='disabled', height=4,
                                  relief='sunken', bd=2)
        self.status_text.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Chord Status Display
        chord_frame = tk.LabelFrame(parent, text="🎵 Chord Status", 
                                   bg='#2a2a2a', fg='#F5DEB3', font=('Cinzel', 11, 'bold'))
        chord_frame.pack(fill='x', padx=10, pady=5)
        
        self.chord_status_label = tk.Label(chord_frame, text="No chord modifiers active\n", 
                                          bg='#2a2a2a', fg='#F5DEB3',
                                          font=('Courier', 9), justify='center')
        self.chord_status_label.pack(padx=10, pady=5)
        
        # ABC Recording Section
        self.abc_frame = tk.LabelFrame(parent, text="📝 ABC NOTATION EXPORT", 
                                 bg='#DAA520', fg='#000000', font=('Cinzel', 12, 'bold'),
                                 relief='raised', bd=3)
        self.abc_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        # ABC controls
        abc_controls = tk.Frame(self.abc_frame, bg='#2a2a2a')
        abc_controls.pack(fill='x', padx=5, pady=5)
        
        self.abc_recording = tk.BooleanVar(value=False)
        self.abc_record_btn = tk.Button(abc_controls, text="🎼 Record ", 
                                       command=self.toggle_abc_recording,
                                       bg='#FFFFFF', fg='#FF0000', 
                                       font=('Cinzel', 9, 'bold'))
        self.abc_record_btn.pack(side='left', padx=5)
        
        abc_load_btn = tk.Button(abc_controls, text="� Load ", 
                                command=self.load_abc_file,
                                bg='#4682B4', fg='#FFFFFF', 
                                font=('Cinzel', 9, 'bold'))
        abc_load_btn.pack(side='left', padx=5)
        
        self.abc_play_btn = tk.Button(abc_controls, text="▶️ Toggle Play ", 
                                     command=self.toggle_abc_playback,
                                     bg='#32CD32', fg='#000000', 
                                     font=('Cinzel', 9, 'bold'))
        self.abc_play_btn.pack(side='left', padx=5)
        
        abc_midi_btn = tk.Button(abc_controls, text="🎹 Export MIDI", 
                                command=self.export_abc_to_midi,
                                bg='#9370DB', fg='#FFFFFF', 
                                font=('Cinzel', 9, 'bold'))
        abc_midi_btn.pack(side='left', padx=5)
        
        abc_save_btn = tk.Button(abc_controls, text="� Save ABC", 
                                command=self.save_abc_file,
                                bg='#DAA520', fg='#000000', 
                                font=('Cinzel', 9, 'bold'))
        abc_save_btn.pack(side='left', padx=5)
        
        abc_clear_btn = tk.Button(abc_controls, text="🗑️ Clear", 
                                 command=self.clear_abc,
                                 bg='#CD5C5C', fg='#FFFFFF', 
                                 font=('Cinzel', 9, 'bold'))
        abc_clear_btn.pack(side='left', padx=5)
        
        # ABC notation display
        self.abc_text = tk.Text(self.abc_frame, bg='#1a1a1a', fg='#98FB98',
                               font=('Courier', 9), height=6,
                               relief='sunken', bd=2)
        self.abc_text.pack(fill='both', expand=True, padx=5, pady=5)

        # MIDI Import & Playback Section
        self.midi_frame = tk.LabelFrame(parent, text="🎵 MIDI FILE PLAYBACK", 
                                 bg='#4B0082', fg='#FFD700', font=('Georgia', 12, 'bold'),
                                 relief='raised', bd=3)
        self.midi_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        # MIDI controls
        midi_controls = tk.Frame(self.midi_frame, bg='#2a2a2a')
        midi_controls.pack(fill='x', padx=5, pady=5)
        
        # First row - File operations
        midi_file_row = tk.Frame(midi_controls, bg='#2a2a2a')
        midi_file_row.pack(fill='x', pady=2)
        
        midi_load_btn = tk.Button(midi_file_row, text="📁 Load MIDI", 
                                command=self.load_midi_file,
                                bg='#4B0082', fg='#FFD700', 
                                font=('Georgia', 9, 'bold'))
        midi_load_btn.pack(side='left', padx=5)
        
        midi_convert_btn = tk.Button(midi_file_row, text="🔄 Convert to ABC", 
                                   command=self.convert_midi_to_abc,
                                   bg='#8A2BE2', fg='#FFFFFF', 
                                   font=('Georgia', 9, 'bold'))
        midi_convert_btn.pack(side='left', padx=5)
        
        self.midi_filename_label = tk.Label(midi_file_row, text="No file loaded", 
                                          bg='#2a2a2a', fg='#CCCCCC', 
                                          font=('Georgia', 8, 'italic'))
        self.midi_filename_label.pack(side='left', padx=10)
        
        # Second row - Playback controls
        midi_playback_row = tk.Frame(midi_controls, bg='#2a2a2a')
        midi_playback_row.pack(fill='x', pady=2)
        
        self.midi_play_btn = tk.Button(midi_playback_row, text="▶️ Play MIDI", 
                                     command=self.play_midi_file,
                                     bg='#228B22', fg='#FFFFFF', 
                                     font=('Georgia', 9, 'bold'),
                                     state='disabled')
        self.midi_play_btn.pack(side='left', padx=5)
        
        self.midi_stop_btn = tk.Button(midi_playback_row, text="⏹️ Stop", 
                                     command=self.stop_midi_playback,
                                     bg='#B22222', fg='#FFFFFF', 
                                     font=('Georgia', 9, 'bold'),
                                     state='disabled')
        self.midi_stop_btn.pack(side='left', padx=5)
        
        # Speed control
        tk.Label(midi_playback_row, text="🕐 Speed:", bg='#2a2a2a', fg='#CCCCCC',
                font=('Georgia', 8)).pack(side='left', padx=(10,2))
        
        self.midi_speed = tk.DoubleVar(value=1.0)
        speed_scale = tk.Scale(midi_playback_row, from_=0.25, to=2.0, resolution=0.25,
                              orient='horizontal', variable=self.midi_speed,
                              bg='#2a2a2a', fg='#CCCCCC', length=100,
                              highlightbackground='#2a2a2a', troughcolor='#4B0082')
        speed_scale.pack(side='left', padx=5)
        
        # MIDI file info display
        self.midi_info_text = tk.Text(self.midi_frame, bg='#1a1a1a', fg='#DA70D6',
                                     font=('Courier', 8), height=4,
                                     relief='sunken', bd=2, state='disabled')
        self.midi_info_text.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Initialize MIDI playback variables
        self.loaded_midi = None
        self.midi_playback_thread = None
        self.midi_playing = False
        
        # Initialize ABC playback variables
        self.abc_playing = False
        self.abc_playback_thread = None

    def setup_key_mappings_tab(self, parent):
        """Setup the key mappings and instrument ranges tab"""
        # Create three-column layout: left for content, middle for image, right for scrollbar
        main_container = tk.Frame(parent, bg='#1a1a1a')
        main_container.pack(fill='both', expand=True, padx=10, pady=10)
        
        # First - image display (leftmost position) - widened by 25%
        image_frame = tk.Frame(main_container, bg='#2a2a2a', relief='sunken', bd=2, width=650)
        image_frame.pack(side='left', fill='y', padx=(0, 10))
        image_frame.pack_propagate(False)  # Maintain the specified width
        
        # Add another bard image
        self.setup_bard_image_2(image_frame)
        
        # Middle - scrollable content
        content_container = tk.Frame(main_container, bg='#1a1a1a')
        content_container.pack(side='left', fill='both', expand=True)
        
        # Create scrollable content
        canvas = tk.Canvas(content_container, bg='#1a1a1a')
        scrollable_frame = tk.Frame(canvas, bg='#1a1a1a')
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        
        # Enable mouse wheel scrolling
        def _on_mouse_wheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        
        def _bind_to_mousewheel(event):
            canvas.bind_all("<MouseWheel>", _on_mouse_wheel)
        
        def _unbind_from_mousewheel(event):
            canvas.unbind_all("<MouseWheel>")
        
        # Bind mouse wheel events when mouse enters/leaves the canvas
        canvas.bind('<Enter>', _bind_to_mousewheel)
        canvas.bind('<Leave>', _unbind_from_mousewheel)
        
        canvas.pack(side="left", fill="both", expand=True)
        
        # Spectrum Analyzer Panel (between content and scrollbar)
        spectrum_frame = tk.Frame(main_container, bg='#2a2a2a', relief='sunken', bd=2, width=400)
        spectrum_frame.pack(side='right', fill='y', padx=(10, 10))
        spectrum_frame.pack_propagate(False)  # Maintain the specified width
        
        # Setup spectrum analyzer
        self.setup_spectrum_analyzer(spectrum_frame)
        
        # Right side - scrollbar
        scrollbar = tk.Scrollbar(main_container, orient="vertical", command=canvas.yview)
        scrollbar.pack(side="right", fill="y")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Title
        title_frame = tk.Frame(scrollable_frame, bg='#1a1a1a')
        title_frame.pack(fill='x', pady=15)
        
        tk.Label(title_frame, text="🎸 LOTRO Key Mappings & Instrument Ranges", 
                font=('Georgia', 18, 'bold'), fg='#DAA520', bg='#1a1a1a').pack()
        
        # Chord Controls Section
        chord_section = tk.LabelFrame(scrollable_frame, text="🎶 CHORD TRIGGERING CONTROLS", 
                                    bg='#4B0082', fg='#FFD700', 
                                    font=('Georgia', 14, 'bold'), bd=3, relief='ridge')
        chord_section.pack(fill='x', padx=20, pady=15)
        
        # Chord explanation
        chord_exp_frame = tk.Frame(chord_section, bg='#4B0082')
        chord_exp_frame.pack(fill='x', padx=10, pady=5)
        
        tk.Label(chord_exp_frame, text="Select chord types below, then play MIDI notes to trigger full chords instead of single notes:", 
                font=('Arial', 11), fg='#F0E68C', bg='#4B0082').pack()
        tk.Label(chord_exp_frame, text="🎵 Check a chord type + Play MIDI note = Automatic chord harmony!", 
                font=('Arial', 10, 'bold'), fg='#FFB6C1', bg='#4B0082').pack(pady=(2,0))
        tk.Label(chord_exp_frame, text="⌨️ CTRL+` cycles patterns", 
                font=('Arial', 9, 'italic'), fg='#32CD32', bg='#4B0082').pack(pady=(2,0))
        
        # Chord selection combobox
        chord_controls_frame = tk.Frame(chord_section, bg='#4B0082')
        chord_controls_frame.pack(padx=15, pady=10)
        
        # Chord selection label and combobox
        tk.Label(chord_controls_frame, text="🎼 Select Chord Type:", 
                font=('Arial', 12, 'bold'), fg='#FFD700', bg='#4B0082').pack(anchor='w', pady=(0,5))
        
        # Create the combobox for chord selection
        self.chord_combobox = ttk.Combobox(chord_controls_frame, 
                                          values=self.chord_types,
                                          state='readonly',
                                          font=('Arial', 11),
                                          width=20)
        self.chord_combobox.pack(anchor='w', pady=5)
        self.chord_combobox.current(0)  # Start with 'Major'
        # self.current_chord_type = 'Major'
        self.chord_combobox.bind('<<ComboboxSelected>>', lambda e: self.on_chord_selection_changed())
        
        # Chord descriptions
        descriptions_frame = tk.Frame(chord_controls_frame, bg='#4B0082')
        descriptions_frame.pack(fill='x', pady=(10, 0))
        
        chord_descriptions = {
            'None': 'Single notes only',
            'Major': 'Major (1-3-5) - Happy, bright sound',
            'Minor': 'Minor (1-♭3-5) - Sad, melancholy sound',
            'Sus2': 'Sus2 (1-2-5) - Open, unresolved sound',
            'Sus4': 'Sus4 (1-4-5) - Suspended, tension sound',
            'Diminished': 'Diminished (1-♭3-♭5) - Dark, unstable sound',
            'Augmented': 'Augmented (1-3-#5) - Dreamy, mysterious sound',
            'Major 7th': 'Major 7th (1-3-5-7) - Jazz, sophisticated sound',
            'Minor 7th': 'Minor 7th (1-♭3-5-♭7) - Smooth, mellow sound'
        }
        
        for chord_type, desc in chord_descriptions.items():
            tk.Label(descriptions_frame, text=f"• {chord_type}: {desc}",
                    font=('Arial', 9), fg='#F0E68C', bg='#4B0082').pack(anchor='w')
        
        # Active chord status
        self.chord_status_frame = tk.Frame(chord_section, bg='#4B0082')
        self.chord_status_frame.pack(fill='x', padx=10, pady=10)
        
        self.chord_status_label_gui = tk.Label(self.chord_status_frame, 
                                              text="No chords selected - Single note mode", 
                                              bg='#4B0082', fg='#F5DEB3',
                                              font=('Arial', 11, 'bold'))
        self.chord_status_label_gui.pack()
        
        # Key Mapping Section
        mapping_section = tk.LabelFrame(scrollable_frame, text="🎹 LOTRO Key Scale (1-8)", 
                                      bg='#2a2a2a', fg='#F5DEB3', 
                                      font=('Georgia', 14, 'bold'), bd=3, relief='ridge')
        mapping_section.pack(fill='x', padx=20, pady=15)
        
        # Key mapping explanation
        exp_frame = tk.Frame(mapping_section, bg='#2a2a2a')
        exp_frame.pack(fill='x', padx=10, pady=5)
        
        tk.Label(exp_frame, text="Each LOTRO instrument uses keys 1-8 for different notes in sequence:", 
                font=('Arial', 11), fg='#F0E68C', bg='#2a2a2a').pack()
        tk.Label(exp_frame, text="🎹 WHITE keys = Natural notes (1-8) | BLACK keys = Flats (Auto CTRL+ = half-step down)", 
                font=('Arial', 10, 'bold'), fg='#FFB6C1', bg='#2a2a2a').pack(pady=(2,0))
        tk.Label(exp_frame, text="No need to hold CTRL manually - black keys automatically send CTRL combinations for flats!", 
                font=('Arial', 9, 'italic'), fg='#98FB98', bg='#2a2a2a').pack(pady=(2,0))
        
        # Key mapping grid with bigger, clearer layout
        mapping_frame = tk.Frame(mapping_section, bg='#2a2a2a')
        mapping_frame.pack(padx=15, pady=15)
        
        # Headers
        headers = ["LOTRO Key", "MIDI Note", "Note Name", "Octave Position"]
        for i, header in enumerate(headers):
            tk.Label(mapping_frame, text=header, font=('Consolas', 12, 'bold'), 
                    fg='#FFD700', bg='#404040', relief='raised', bd=2, 
                    width=15).grid(row=0, column=i, padx=2, pady=2, sticky='ew')
        
        # Key mappings - the standard LOTRO scale with black keys
        key_mappings = [
            # White keys (natural notes)
            ("1", "C4 (60)", "Middle C", "4th"),
            ("2", "D4 (62)", "D", "4th"),
            ("3", "E4 (64)", "E", "4th"),
            ("4", "F4 (65)", "F", "4th"),
            ("5", "G4 (67)", "G", "4th"),
            ("6", "A4 (69)", "A", "4th"),
            ("7", "B4 (71)", "B", "4th"),
            ("8", "C5 (72)", "High C", "5th"),
            # Black keys (sharps/flats) - automatically trigger CTRL combinations (half-step down from white key)
            ("CTRL+1", "B3 (59)", "B", "3rd"),
            ("CTRL+2", "C#4 (61)", "C#", "4th"),
            ("CTRL+3", "D#4 (63)", "D#", "4th"),
            ("CTRL+5", "F#4 (66)", "F#", "4th"),
            ("CTRL+6", "G#4 (68)", "G#", "4th"),
            ("CTRL+7", "A#4 (70)", "A#", "4th"),
            ("CTRL+8", "C#5 (73)", "C#", "5th")
        ]
        
        for i, (lotro_key, midi_note, note_name, octave) in enumerate(key_mappings, 1):
            # Different colors for white keys vs black keys
            is_black_key = "CTRL+" in lotro_key
            if is_black_key:
                row_color = '#1a1a1a'  # Darker for black keys
                key_color = '#FFD700'  # Gold for CTRL combinations
                note_color = '#FFA500'  # Orange for sharp notes
            else:
                row_color = '#3a3a3a' if i % 2 == 0 else '#2a2a2a'
                key_color = '#90EE90'  # Light green for regular keys
                note_color = '#ADD8E6'  # Light blue for natural notes
            
            tk.Label(mapping_frame, text=lotro_key, font=('Consolas', 12, 'bold'), 
                    fg=key_color, bg=row_color, width=15, 
                    relief='raised' if is_black_key else 'sunken', bd=1).grid(row=i, column=0, padx=2, pady=1, sticky='ew')
            tk.Label(mapping_frame, text=midi_note, font=('Consolas', 11), 
                    fg='#FFFFFF', bg=row_color, width=15,
                    relief='sunken', bd=1).grid(row=i, column=1, padx=2, pady=1, sticky='ew')
            tk.Label(mapping_frame, text=note_name, font=('Consolas', 11), 
                    fg=note_color, bg=row_color, width=15,
                    relief='sunken', bd=1).grid(row=i, column=2, padx=2, pady=1, sticky='ew')
            tk.Label(mapping_frame, text=octave, font=('Consolas', 11), 
                    fg='#DDA0DD', bg=row_color, width=15,
                    relief='sunken', bd=1).grid(row=i, column=3, padx=2, pady=1, sticky='ew')
        
        # Instrument Ranges Section
        ranges_section = tk.LabelFrame(scrollable_frame, text="🎼 LOTRO Instrument Ranges", 
                                     bg='#2a2a2a', fg='#F5DEB3', 
                                     font=('Georgia', 14, 'bold'), bd=3, relief='ridge')
        ranges_section.pack(fill='x', padx=20, pady=15)
        
        # Instrument data with accurate LOTRO ranges
        instruments = [
            {
                'name': '🎸 Lute',
                'range': '3 Octaves',
                'lowest': 'C4 (60)',
                'highest': 'C7 (96)',
                'description': 'Versatile string instrument',
                'color': '#8B4513'
            },
            {
                'name': '🪈 Flute',
                'range': '3 Octaves',
                'lowest': 'C5 (72)',
                'highest': 'C8 (108)',
                'description': 'High-pitched woodwind',
                'color': '#CD853F'
            },
            {
                'name': '🎺 Horn',
                'range': '3 Octaves',
                'lowest': 'C3 (48)',
                'highest': 'C6 (84)',
                'description': 'Mid-range brass instrument',
                'color': '#DAA520'
            },
            {
                'name': '🎹 Harp',
                'range': '4 Octaves',
                'lowest': 'C2 (36)',
                'highest': 'C6 (84)',
                'description': 'Wide range plucked string',
                'color': '#F0E68C'
            },
            {
                'name': '🎻 Fiddle',
                'range': '3 Octaves',
                'lowest': 'G4 (67)',
                'highest': 'G7 (103)',
                'description': 'Bowed string instrument',
                'color': '#D2B48C'
            },
            {
                'name': '� Clarinet',
                'range': '3 Octaves',
                'lowest': 'E4 (64)',
                'highest': 'E7 (100)',
                'description': 'Smooth woodwind with warm tone',
                'color': '#DEB887'
            },
            {
                'name': '� Oboe',
                'range': '3 Octaves',
                'lowest': 'Bb4 (70)',
                'highest': 'Bb7 (106)',
                'description': 'Double-reed woodwind, bright tone',
                'color': '#CD5C5C'
            },
            {
                'name': '🎺 Pibgorn',
                'range': '2 Octaves',
                'lowest': 'G5 (79)',
                'highest': 'G7 (103)',
                'description': 'Welsh hornpipe, unique folk sound',
                'color': '#BC8F8F'
            },
            {
                'name': '🥁 Drums',
                'range': 'Percussion',
                'lowest': 'Various',
                'highest': 'Various',
                'description': 'Rhythmic percussion kit',
                'color': '#A0522D'
            }
        ]
        
        # Create instrument grid
        inst_frame = tk.Frame(ranges_section, bg='#2a2a2a')
        inst_frame.pack(padx=10, pady=10)
        
        # Grid headers
        grid_headers = ["Instrument", "Range", "Lo Note", "Hi Note", "Description"]
        for i, header in enumerate(grid_headers):
            width = 30 if i == 4 else 12  # Make description column much wider
            tk.Label(inst_frame, text=header, font=('Consolas', 10, 'bold'), 
                    fg='#FFD700', bg='#404040', relief='raised', bd=1, 
                    width=width).grid(row=0, column=i, padx=1, pady=1, sticky='ew')
        
        # Instrument rows
        for i, instrument in enumerate(instruments, 1):
            # Alternate row colors
            row_color = '#3a3a3a' if i % 2 == 0 else '#2a2a2a'
            
            tk.Label(inst_frame, text=instrument['name'], 
                    font=('Consolas', 10, 'bold'), fg='#000000', 
                    bg=instrument['color'], width=12, relief='raised', bd=1).grid(
                    row=i, column=0, padx=1, pady=1, sticky='ew')
            
            tk.Label(inst_frame, text=instrument['range'], 
                    font=('Consolas', 9), fg='#FFFFFF', 
                    bg=row_color, width=12, relief='sunken', bd=1).grid(
                    row=i, column=1, padx=1, pady=1, sticky='ew')
            
            tk.Label(inst_frame, text=instrument['lowest'], 
                    font=('Consolas', 9), fg='#FFB6C1', 
                    bg=row_color, width=12, relief='sunken', bd=1).grid(
                    row=i, column=2, padx=1, pady=1, sticky='ew')
            
            tk.Label(inst_frame, text=instrument['highest'], 
                    font=('Consolas', 9), fg='#87CEEB', 
                    bg=row_color, width=12, relief='sunken', bd=1).grid(
                    row=i, column=3, padx=1, pady=1, sticky='ew')
            
            tk.Label(inst_frame, text=instrument['description'], 
                    font=('Arial', 9), fg='#F5F5DC', 
                    bg=row_color, width=30, wraplength=280, 
                    relief='sunken', bd=1).grid(
                    row=i, column=4, padx=1, pady=1, sticky='ew')

        # Usage tips section
        tips_section = tk.LabelFrame(scrollable_frame, text="💡 Usage Tips", 
                                   bg='#2a2a2a', fg='#F5DEB3', 
                                   font=('Georgia', 12, 'bold'), bd=2, relief='ridge')
        tips_section.pack(fill='x', padx=20, pady=15)
        
        tips_text = """
🎵 Press Ctrl+M in LOTRO to open the music panel and select your instrument
🎹 Each instrument transposes notes based on your Music skill level
🎸 Use the arpeggiator on the main tab for automatic chord progressions
🥁 Drums have special mappings - experiment with different MIDI notes
🎺 The harp has the widest range and works best with complex arrangements
📝 Higher Music skill = access to more octaves on each instrument
        """.strip()
        
        tk.Label(tips_section, text=tips_text, font=('Arial', 10), 
                fg='#F5F5DC', bg='#2a2a2a', justify='left').pack(padx=15, pady=10)

    def setup_bard_image_2(self, parent):
        """Setup second bard image in key mappings tab"""
        try:
            # Try multiple image paths
            possible_paths = [
                os.path.join(os.path.dirname(__file__), "bard w moog.png"),
                os.path.join(os.path.dirname(__file__), "bard_background.png"),
                os.path.join(os.path.dirname(__file__), "bard_keyboard.png"),
                os.path.join(os.path.dirname(__file__), "bard_2.png")
            ]
            
            image_loaded = False
            for image_path in possible_paths:
                if os.path.exists(image_path):
                    try:
                        # Load and resize image to fit the wider left panel
                        image = Image.open(image_path)
                        # Resize to fit the wider panel nicely (25% larger)
                        image = image.resize((600, 520), Image.Resampling.LANCZOS)
                        photo = ImageTk.PhotoImage(image)
                        
                        # Create image label
                        image_label = tk.Label(parent, image=photo, bg='#2a2a2a', relief='sunken', bd=2)
                        image_label.image = photo  # Keep a reference
                        image_label.pack(pady=10)
                        
                        image_loaded = True
                        break
                    except Exception as img_error:
                        continue
            
            if image_loaded:
                # Add caption
                caption = tk.Label(parent, text="🎹 Master of Musical Arts 🎵", 
                                  font=('Georgia', 12, 'bold'), fg='#DAA520', 
                                  bg='#2a2a2a', wraplength=350)
                caption.pack(pady=(0, 5))
                
                description = tk.Label(parent, text="\"With MIDI controller in hand,\nthe modern bard brings ancient\nmelodies to life in Middle-earth\"", 
                                      font=('Georgia', 9, 'italic'), fg='#F5DEB3', 
                                      bg='#2a2a2a', justify='center', wraplength=350)
                description.pack(pady=(0, 10))
            else:
                # Beautiful fallback if no image found
                art_frame = tk.Frame(parent, bg='#DAA520', relief='raised', bd=3)
                art_frame.pack(pady=20, padx=10, fill='x')
                
                ascii_art = tk.Label(art_frame, text="""🎼 ♪ ♫ ♪ ♫ 🎼
                
    ╭─────────────╮
    │  🎹 MIDI 🎸  │
    │    BARD     │
    │  CONTROLLER │
    ╰─────────────╯
    
♪ ♫ ♪ ♫ ♪ ♫ ♪ ♫""", 
                                 font=('Courier', 10, 'bold'), fg='#000000', 
                                 bg='#DAA520', justify='center')
                ascii_art.pack(pady=15, padx=15)
                
                caption = tk.Label(parent, text="🎵 Ready to Rock Middle-earth! 🎵", 
                                  font=('Georgia', 11, 'bold'), fg='#DAA520', 
                                  bg='#2a2a2a', wraplength=350)
                caption.pack(pady=(10, 0))
                
        except Exception as e:
            # Minimal error fallback
            print(f"Image setup error: {e}")
            simple_label = tk.Label(parent, text="🎼\n\nMIDI Bard\nController\n\n🎸", 
                                   font=('Georgia', 14, 'bold'), fg='#DAA520', 
                                   bg='#2a2a2a', justify='center')
            simple_label.pack(expand=True)
    
    def setup_spectrum_analyzer(self, parent):
        """Setup the real-time frequency spectrum analyzer"""
        # Title
        title_label = tk.Label(parent, text="🎵 Real-Time Spectrum", 
                              font=('Georgia', 14, 'bold'), fg='#DAA520', bg='#2a2a2a')
        title_label.pack(pady=10)
        
        # Subtitle
        subtitle_label = tk.Label(parent, text="Volume vs Pitch", 
                                 font=('Georgia', 10, 'italic'), fg='#F5DEB3', bg='#2a2a2a')
        subtitle_label.pack(pady=(0, 10))
        
        # Canvas for spectrum display
        canvas_frame = tk.Frame(parent, bg='#1a1a1a', relief='sunken', bd=2)
        canvas_frame.pack(fill='both', expand=True, padx=10, pady=5)
        
        self.spectrum_canvas = tk.Canvas(canvas_frame, bg='#000000', 
                                        width=360, height=400)
        self.spectrum_canvas.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Controls frame
        controls_frame = tk.Frame(parent, bg='#2a2a2a')
        controls_frame.pack(fill='x', padx=10, pady=5)
        
        # Enable/Disable button
        self.spectrum_enabled = tk.BooleanVar(value=True)
        spectrum_toggle = tk.Checkbutton(controls_frame, text="📊 Enable Spectrum", 
                                        variable=self.spectrum_enabled, 
                                        bg='#2a2a2a', fg='#F5DEB3',
                                        font=('Georgia', 9, 'bold'), 
                                        selectcolor='#8B4513',
                                        command=self.toggle_spectrum_analyzer)
        spectrum_toggle.pack(pady=5)
        
        # Sensitivity scale
        tk.Label(controls_frame, text="🎚️ Sensitivity:", bg='#2a2a2a', fg='#F5DEB3',
                font=('Georgia', 9)).pack()
        
        self.spectrum_sensitivity = tk.DoubleVar(value=1.0)
        sensitivity_scale = tk.Scale(controls_frame, from_=0.1, to=3.0, resolution=0.1,
                                   orient='horizontal', variable=self.spectrum_sensitivity,
                                   bg='#2a2a2a', fg='#F5DEB3', length=200,
                                   highlightbackground='#2a2a2a', troughcolor='#8B4513')
        sensitivity_scale.pack(pady=5)
        
        # Info labels
        info_frame = tk.Frame(parent, bg='#2a2a2a')
        info_frame.pack(fill='x', padx=10, pady=5)
        
        tk.Label(info_frame, text="💡 Visual Feedback:", 
                font=('Georgia', 9, 'bold'), fg='#DAA520', bg='#2a2a2a').pack()
        
        tk.Label(info_frame, text="• Height = Note Volume\n• Color = Note Intensity\n• Width = Frequency Range", 
                font=('Arial', 8), fg='#F5F5DC', bg='#2a2a2a', justify='left').pack(pady=2)
        
        # Start spectrum analyzer
        self.start_spectrum_analyzer()
        
    def setup_midi_ports(self):
        """Scan and populate available MIDI ports"""
        try:
            ports = mido.get_input_names()
            # Filter for KONTROL ports first, then others (avoid UMC404HD)
            kontrol_ports = [p for p in ports if "KONTROL" in p.upper()]
            other_ports = [p for p in ports if "KONTROL" not in p.upper()]
            
            all_ports = kontrol_ports + other_ports
            self.port_dropdown['values'] = all_ports
            
            if all_ports:
                self.port_dropdown.current(0)
                self.log_status(f"Found {len(all_ports)} MIDI ports")
            else:
                self.log_status("No MIDI ports found!")
                
        except Exception as e:
            self.log_status(f"Error scanning MIDI ports: {e}")
            
    def log_status(self, message):
        """Add message to status display"""
        self.status_text.config(state='normal')
        timestamp = time.strftime("%H:%M:%S")
        self.status_text.insert('end', f"[{timestamp}] {message}\n")
        self.status_text.see('end')
        self.status_text.config(state='disabled')

        # for message in self.midi_port.iter_pending():
        # # --- NEW: Use C1/D1 to scroll ARP and chord comboboxes ---
        #     if message.type == 'note_on' and message.velocity > 0:
        #         if message.note == 24:  # C1 - scroll UP
        #             self.root.after(0, self.scroll_control_combobox, -1)
        #             continue
        #         elif message.note == 26:  # D1 - scroll DOWN
        #             self.root.after(0, self.scroll_control_combobox, 1)
        #             continue
        # # ...existing code...
        
    def start_midi(self):
        """Start MIDI input processing with countdown"""
        port_name = self.port_var.get()
        if not port_name:
            messagebox.showerror("Error", "Please select a MIDI port")
            return
            
        # Start countdown in separate thread
        countdown_thread = threading.Thread(target=self.countdown_and_start, args=[port_name], daemon=True)
        countdown_thread.start()
        
    def countdown_and_start(self, port_name):
        """Countdown before starting MIDI"""
        try:
            # Disable start button during countdown
            self.start_btn.config(state='disabled', text="Starting...", bg='#ff9800')
            
            # 3-second countdown with visual display
            for i in range(3, 0, -1):
                self.countdown_label.config(text=f"⏰ Starting in {i}...\n🎮 Click into LOTRO now!")
                self.log_status(f"🕐 Starting in {i} seconds... (Click into LOTRO now!)")
                self.root.update_idletasks()
                time.sleep(1)
                
            # Final ready message
            self.countdown_label.config(text="🎯 READY! 🎹", fg='#4CAF50')
            self.log_status("🎯 MIDI Active - Ready to play!")
            self.root.update_idletasks()
            time.sleep(0.5)
            
            # Clear countdown display
            self.countdown_label.config(text="")
            
            # Check if port is still available
            available_ports = mido.get_input_names()
            if port_name not in available_ports:
                # Refresh the port list
                self.setup_midi_ports()  # Refresh the dropdown
                raise Exception(f"MIDI port '{port_name}' is no longer available. Available ports: {available_ports}")
            
            # Now start MIDI
            self.midi_port = mido.open_input(port_name)
            self.is_running = True
            
            # Start MIDI processing thread
            self.midi_thread = threading.Thread(target=self.process_midi, daemon=True)
            self.midi_thread.start()
            
            # Update UI
            self.start_btn.config(text="▶️ Start MIDI", bg='#4CAF50')
            self.stop_btn.config(state='normal')
            self.log_status(f"✓ MIDI Active on: {port_name}")
            
        except Exception as e:
            error_msg = str(e)
            # Provide helpful suggestions based on the error
            if "error creating Windows MM MIDI input port" in error_msg:
                suggestion = "\n\nSuggestions:\n• Check if your MIDI device is properly connected\n• Try disconnecting and reconnecting your MIDI device\n• Close other MIDI applications that might be using the port\n• Select a different MIDI port from the dropdown"
                error_msg += suggestion
            
            messagebox.showerror("MIDI Port Error", f"Failed to open MIDI port: {error_msg}")
            self.log_status(f"✗ Failed to open MIDI port: {e}")
            self.start_btn.config(state='normal', text="▶️ Start MIDI", bg='#4CAF50')
            self.countdown_label.config(text="")
            
    def stop_midi(self):
        """Stop MIDI input processing and all playback"""
        self.is_running = False
        self.arp_running = False
        
        # Stop MIDI file playback
        if hasattr(self, 'midi_playing') and self.midi_playing:
            self.stop_midi_playback()
        
        # Stop ABC playback
        if hasattr(self, 'abc_playing') and self.abc_playing:
            self.stop_abc_playback()
        
        # Stop pygame mixer
        try:
            import pygame
            if pygame.mixer.get_init():
                pygame.mixer.stop()
                pygame.mixer.quit()
        except Exception:
            pass  # pygame might not be loaded
        
        if self.midi_port:
            self.midi_port.close()
            self.midi_port = None
            
        self.start_btn.config(state='normal')
        self.stop_btn.config(state='disabled')
        self.log_status("⏹ All music stopped")
        
    def process_midi(self):
        """Process incoming MIDI messages"""
        while self.is_running and self.midi_port:
            try:
                for message in self.midi_port.iter_pending():
                # Only scroll on note_on with velocity > 0
                    if message.type == 'note_on' and message.velocity > 0:
                        if message.note == 24:  # C1 - scroll UP
                            self.root.after(0, self.scroll_control_combobox, -1)
                            self.log_status("C1 pressed: Scroll UP")
                            continue
                        elif message.note == 26:  # D1 - scroll DOWN
                            self.root.after(0, self.scroll_control_combobox, 1)
                            self.log_status("D1 pressed: Scroll DOWN")
                            continue
                        elif message.note == 25:  # C#1 - toggle ARP enable
                            if self.arp_enabled.get():
                                # ARP is ON: turn OFF and switch to main tab, set chord type to None
                                self.root.after(0, self.arp_enabled.set, False)
                                self.root.after(0, self.toggle_arpeggiator)
                                self.root.after(0, lambda: self.notebook.select(0))
                                self.root.after(0, lambda: self.chord_combobox.current(0))  # Set chord type to 'None'
                                self.root.after(0, self.on_chord_selection_changed)
                                self.log_status("C#1 pressed: ARP OFF, switched to main tab, chord type set to None")
                            else:
                                # ARP is OFF: turn ON (stay on main tab)
                                self.root.after(0, self.arp_enabled.set, True)
                                self.root.after(0, self.toggle_arpeggiator)
                                self.log_status("C#1 pressed: ARP ON")
                            continue
                        elif message.note == 27:  # D#1 - switch to chord tab and turn ARP off
                            self.root.after(0, self.arp_enabled.set, False)
                            self.root.after(0, self.toggle_arpeggiator)
                            self.root.after(0, lambda: self.notebook.select(1))
                            self.log_status("D#1 pressed: ARP OFF, switched to chord tab")
                            continue
                    # --- Ribbon controller (CC) changes ARP BPM ---
                    if message.type == 'control_change':
                        # Replace 16 with your ribbon's CC number if needed
                        if message.control == 16:  # CC 16 is a common ribbon/fader
                            # MIDI CC value is 0-127, map to BPM 60-200
                            bpm = int(60 + (message.value / 127) * 140)
                            self.arp_speed.set(bpm)
                            self.log_status(f"🎚️ Ribbon controller set ARP BPM to {bpm}")

                    if message.type == 'note_on' and message.velocity > 0:
                        # Update spectrum analyzer
                        self.update_note_spectrum(message.note, message.velocity, note_on=True)
                        
                        # Record for ABC notation
                        self.record_abc_note(message.note, message.velocity, note_on=True)
                        
                        if self.arp_enabled.get():
                            self.handle_arp_note_on(message.note)
                        else:
                            self.handle_note_on(message.note)
                            
                    elif message.type == 'note_off' or (message.type == 'note_on' and message.velocity == 0):
                        # Update spectrum analyzer
                        self.update_note_spectrum(message.note, 0, note_on=False)
                        
                        # Record note off for ABC notation
                        self.record_abc_note(message.note, 0, note_on=False)
                        
                        if self.arp_enabled.get():
                            self.handle_arp_note_off(message.note)
                        else:
                            self.handle_note_off(message.note)
                            
                time.sleep(0.001)  # Small delay to prevent CPU overload
                
            except Exception as e:
                self.log_status(f"MIDI processing error: {e}")
                break
    def toggle_arp_checkbox(self):
        """Toggle the ARP enabler checkbox on the main tab"""
        current = self.arp_enabled.get()
        self.arp_enabled.set(not current)
        self.toggle_arpeggiator()
        self.log_status(f"ARP {'enabled' if not current else 'disabled'} via MIDI control")

    def handle_note_on(self, note):
        """Handle regular note on - now supports CTRL combinations for black keys and chord triggering"""
        key_mapping = self.action_map.get(note)
        if key_mapping:
            note_name = self.get_note_name(note)
            
            # Check if chord type is active
            if self.current_chord_type != 'None':
                try:
                    # Play chord instead of single note
                    chord_notes = self.play_chord(note)
                    
                    # Detailed debugging for Major 7th chords specifically
                    if self.current_chord_type == 'Major 7th':
                        self.log_status(f"🔍 DEBUGGING {note_name} {self.current_chord_type}:")
                        self.log_status(f"   Pattern: {self.chord_patterns.get(self.chord_type_map.get(self.current_chord_type))}")
                        self.log_status(f"   Calculated notes: {chord_notes}")
                        for i, chord_note in enumerate(chord_notes):
                            chord_note_name = self.get_note_name(chord_note)
                            mapping = self.action_map.get(chord_note)
                            interval_names = ["Root", "3rd", "5th", "7th"]
                            interval = interval_names[i] if i < len(interval_names) else f"Note {i+1}"
                            status = "✓" if mapping else "❌ NO MAPPING"
                            if mapping and isinstance(mapping, tuple):
                                status += f" (COMPLEX: {mapping})"
                            self.log_status(f"   {interval}: {chord_note} ({chord_note_name}) -> {mapping} {status}")
                    elif note in [50, 52, 57]:  # D3, E3, A3 - the problematic root notes
                        self.log_status(f"🔍 DEBUGGING {note_name} Major:")
                        self.log_status(f"   Root: {note} ({note_name}) -> {self.action_map.get(note)}")
                        for i, chord_note in enumerate(chord_notes):
                            chord_note_name = self.get_note_name(chord_note)
                            mapping = self.action_map.get(chord_note)
                            interval_names = ["Root", "3rd", "5th", "7th"]
                            interval = interval_names[i] if i < len(interval_names) else f"Note {i+1}"
                            self.log_status(f"   {interval}: {chord_note} ({chord_note_name}) -> {mapping}")
                    
                    # The issue: SHIFT+CTRL combinations work for single notes but fail in chords
                    # For Major 7th chords with problematic roots, substitute SHIFT+CTRL 7th notes 
                    # with their SHIFT equivalents (one semitone lower)
                    
                    adjusted_chord_notes = []
                    for chord_note in chord_notes:
                        mapping = self.action_map.get(chord_note)
                        
                        # Only substitute the 7th note if it uses SHIFT+CTRL in Major 7th chords
                        # Don't substitute 3rd intervals as that changes major to minor
                        if (self.current_chord_type == 'Major 7th' and 
                            isinstance(mapping, tuple) and mapping[0] == 'shift+ctrl'):
                            
                            # Check if this is the 7th interval (11 semitones from root)
                            root_note = chord_notes[0]  # First note is always the root
                            interval_from_root = chord_note - root_note
                            
                            # Only substitute if this is the 7th interval (11 semitones)
                            if interval_from_root == 11:
                                substitute_note = chord_note - 1
                                substitute_mapping = self.action_map.get(substitute_note)
                                if substitute_mapping:
                                    self.log_status(f"🔄 Substituting 7th note {chord_note} with {substitute_note}")
                                    adjusted_chord_notes.append(substitute_note)
                                else:
                                    adjusted_chord_notes.append(chord_note)
                            else:
                                # Keep 3rd and 5th intervals unchanged to preserve chord quality
                                adjusted_chord_notes.append(chord_note)
                        else:
                            adjusted_chord_notes.append(chord_note)
                    
                    # Send the adjusted chord notes
                    for i, chord_note in enumerate(adjusted_chord_notes):
                        chord_key_mapping = self.action_map.get(chord_note)
                        if chord_key_mapping:
                            if i > 0:
                                time.sleep(0.02)  # Small delay between notes
                            
                            self.send_note_key(chord_note, chord_key_mapping, press=True)
                        else:
                            self.log_status(f"❌ No mapping for chord note {chord_note} ({self.get_note_name(chord_note)})")
                    
                    # Log chord information
                    chord_note_names = [self.get_note_name(n) for n in chord_notes]
                    self.log_status(f"🎵🎶 {self.current_chord_type.upper()} CHORD: {' + '.join(chord_note_names)} (PRESS)")
                except Exception as e:
                    self.log_status(f"ERROR in chord processing: {e}")
                    # Fallback to single note if chord fails
                    self.send_note_key(note, key_mapping, press=True)
            else:
                # Single note play - use original simple logic
                if isinstance(key_mapping, tuple):
                    modifier, key_code = key_mapping
                    if modifier == 'ctrl':
                        # Handle CTRL + key combination for sharps/flats
                        self.send_ctrl_key(key_code, press=True)
                        key_char = f"CTRL+{chr(key_code)}" if 32 <= key_code <= 126 else f"CTRL+VK_{key_code}"
                        self.log_status(f"🎵♯ {note_name} → {key_char} (PRESS)")
                        self.update_note_status_display(note, "PRESS", key_char)
                    elif modifier == 'shift':
                        # Handle SHIFT + key combination for extended range
                        self.send_shift_key(key_code, press=True)
                        key_char = f"SHIFT+{chr(key_code)}" if 32 <= key_code <= 126 else f"SHIFT+VK_{key_code}"
                        self.log_status(f"🎵↗ {note_name} → {key_char} (PRESS)")
                        self.update_note_status_display(note, "PRESS", key_char)
                    elif modifier == 'shift+ctrl':
                        # Handle SHIFT+CTRL + key combination for higher octave sharps/flats
                        self.send_shift_ctrl_key(key_code, press=True)
                        key_char = f"SHIFT+CTRL+{chr(key_code)}" if 32 <= key_code <= 126 else f"SHIFT+CTRL+VK_{key_code}"
                        self.log_status(f"🎵♯↗ {note_name} → {key_char} (PRESS)")
                        self.update_note_status_display(note, "PRESS", key_char)
                else:
                    # Handle regular key press - original working method
                    self.send_key(key_mapping, press=True)
                    key_char = chr(key_mapping) if 32 <= key_mapping <= 126 else f"VK_{key_mapping}"
                    self.log_status(f"🎵 {note_name} → {key_char} (PRESS)")
                    self.update_note_status_display(note, "PRESS", key_char)
    
    def send_note_key(self, note, key_mapping, press=True):
        """Helper function to send a key for a specific note"""
        try:
            note_name = self.get_note_name(note)
            
            if isinstance(key_mapping, tuple):
                modifier, key_code = key_mapping
                if modifier == 'ctrl':
                    # Handle CTRL + key combination for sharps/flats
                    self.send_ctrl_key(key_code, press=press)
                    key_char = f"CTRL+{chr(key_code)}" if 32 <= key_code <= 126 else f"CTRL+VK_{key_code}"
                    action_text = "PRESS" if press else "RELEASE"
                    self.log_status(f"🎵♯ {note_name} → {key_char} ({action_text})")
                    self.update_note_status_display(note, action_text, key_char)
                elif modifier == 'shift':
                    # Handle SHIFT + key combination for extended range
                    self.send_shift_key(key_code, press=press)
                    key_char = f"SHIFT+{chr(key_code)}" if 32 <= key_code <= 126 else f"SHIFT+VK_{key_code}"
                    action_text = "PRESS" if press else "RELEASE"
                    self.log_status(f"🎵↗ {note_name} → {key_char} ({action_text})")
                    self.update_note_status_display(note, action_text, key_char)
                elif modifier == 'shift+ctrl':
                    # Handle SHIFT+CTRL + key combination for higher octave sharps/flats
                    self.send_shift_ctrl_key(key_code, press=press)
                    key_char = f"SHIFT+CTRL+{chr(key_code)}" if 32 <= key_code <= 126 else f"SHIFT+CTRL+VK_{key_code}"
                    action_text = "PRESS" if press else "RELEASE"
                    self.log_status(f"🎵♯↗ {note_name} → {key_char} ({action_text})")
                    self.update_note_status_display(note, action_text, key_char)
                elif modifier == 'alt':
                    # Handle ALT + key combination for extended range
                    self.send_alt_key(key_code, press=press)
                    key_char = f"ALT+{chr(key_code)}" if 32 <= key_code <= 126 else f"ALT+VK_{key_code}"
                    action_text = "PRESS" if press else "RELEASE"
                    self.log_status(f"🎵⎇ {note_name} → {key_char} ({action_text})")
                    self.update_note_status_display(note, action_text, key_char)

            else:
                # Handle regular key press
                self.send_key(key_mapping, press=press)
                key_char = chr(key_mapping) if 32 <= key_mapping <= 126 else f"VK_{key_mapping}"
                action_text = "PRESS" if press else "RELEASE"
                self.log_status(f"🎵 {note_name} → {key_char} ({action_text})")
                self.update_note_status_display(note, action_text, key_char)
        except Exception as e:
            self.log_status(f"ERROR in send_note_key: {e} for note {note} ({self.get_note_name(note)})")
            
    def handle_note_off(self, note):
        """Handle regular note off - now supports CTRL combinations for black keys and chord releases"""
        key_mapping = self.action_map.get(note)
        if key_mapping:
            note_name = self.get_note_name(note)
            # Use the same release method as working midi2key.py
            time.sleep(0.001)  # 1ms delay to ensure key press was processed
            
            # Check if we need to release a chord or single note
            # For chord releases, we need to release all chord notes that were pressed
            if hasattr(self, 'last_chord_notes') and note in getattr(self, 'last_chord_notes', []):
                # Get chord note names before clearing the list
                chord_note_names = [self.get_note_name(n) for n in self.last_chord_notes if self.action_map.get(n)]
                
                # Release all notes from the last chord that included this root note
                for chord_note in self.last_chord_notes:
                    chord_key_mapping = self.action_map.get(chord_note)
                    if chord_key_mapping:
                        self.send_note_key(chord_note, chord_key_mapping, press=False)
                        # Update spectrum for chord note release
                        self.update_note_spectrum(chord_note, 0, False)
                        
                # Log chord release
                if chord_note_names:
                    self.log_status(f"🎵🎶 CHORD RELEASE: {' + '.join(chord_note_names)}")
                    
                # Clear the last chord notes
                self.last_chord_notes = []
            else:
                # Single note release - use original simple logic
                if isinstance(key_mapping, tuple):
                    modifier, key_code = key_mapping
                    if modifier == 'ctrl':
                        # Handle CTRL + key combination release for sharps/flats
                        self.send_ctrl_key(key_code, press=False)
                        key_char = f"CTRL+{chr(key_code)}" if 32 <= key_code <= 126 else f"CTRL+VK_{key_code}"
                        self.log_status(f"🎵♯ {note_name} → {key_char} (RELEASE)")
                        self.update_note_status_display(note, "RELEASE", key_char)
                    elif modifier == 'shift':
                        # Handle SHIFT + key combination release for extended range
                        self.send_shift_key(key_code, press=False)
                        key_char = f"SHIFT+{chr(key_code)}" if 32 <= key_code <= 126 else f"SHIFT+VK_{key_code}"
                        self.log_status(f"🎵↗ {note_name} → {key_char} (RELEASE)")
                        self.update_note_status_display(note, "RELEASE", key_char)
                else:
                    # Handle regular key release - original working method
                    self.send_key(key_mapping, press=False)
                    key_char = chr(key_mapping) if 32 <= key_mapping <= 126 else f"VK_{key_mapping}"
                    self.log_status(f"🎵 {note_name} → {key_char} (RELEASE)")
                    self.update_note_status_display(note, "RELEASE", key_char)
            
            # Force flush any pending messages
            windll.user32.UpdateWindow(self.find_lotro_window() or 0)
            
    def handle_arp_note_on(self, note):
        """Handle note on for arpeggiator"""
        if note not in self.arp_notes:
            self.arp_notes.append(note)
            self.update_chord_display()
            
        if not self.arp_running:
            self.start_arpeggiator()
            
    def handle_arp_note_off(self, note):
        """Handle note off for arpeggiator"""
        if note in self.arp_notes:
            self.arp_notes.remove(note)
            self.update_chord_display()
            
        if not self.arp_notes:
            self.stop_arpeggiator()
            
    def update_chord_display(self):
        """Update the chord display"""
        self.chord_display.config(state='normal')
        self.chord_display.delete(1.0, 'end')
        
        if self.arp_notes:
            chord_text = "Current Notes:\n"
            for note in sorted(self.arp_notes):
                note_name = self.get_note_name(note)
                chord_text += f"• {note_name} (MIDI {note})\n"
        else:
            chord_text = "No notes being held"
            
        self.chord_display.insert(1.0, chord_text)
        self.chord_display.config(state='disabled')
        
    def update_note_status_display(self, note, action, key_char):
        """Update note status display with raw MIDI output (non-arp mode)"""
        if self.arp_enabled.get():
            return  # Don't update in arp mode, use chord display instead
            
        self.chord_display.config(state='normal')
        
        # Keep a rolling log of recent MIDI events (without timestamp)
        note_name = self.get_note_name(note)
        event_line = f"{note_name} → {key_char} ({action})\n"
        
        # Insert at the top and limit to ~35 lines
        self.chord_display.insert(1.0, event_line)
        
        # Keep only recent events (limit to prevent overflow)
        content = self.chord_display.get(1.0, 'end')
        lines = content.split('\n')
        if len(lines) > 37:  # Keep last 35 events plus some buffer
            limited_content = '\n'.join(lines[:35])
            self.chord_display.delete(1.0, 'end')
            self.chord_display.insert(1.0, limited_content)
        
        self.chord_display.config(state='disabled')
        # Scroll to top to show newest events
        self.chord_display.see(1.0)
        
    def initialize_note_status_display(self):
        """Initialize the note status display with appropriate message"""
        self.chord_display.config(state='normal')
        if self.arp_enabled.get():
            message = "Arpeggiator Mode: Hold notes to see chord\nPress multiple keys to create chords"
        else:
            message = "Normal Mode: Raw MIDI output will appear here\nPlay notes to see MIDI → Key mapping"
        
        self.chord_display.insert(1.0, message)
        self.chord_display.config(state='disabled')
        
    def start_arpeggiator(self):
        """Start the arpeggiator"""
        if self.arp_running:
            return
            
        self.arp_running = True
        self.arp_thread = threading.Thread(target=self.run_arpeggiator, daemon=True)
        self.arp_thread.start()
        self.log_status("🎶 Arpeggiator started")
        
    def stop_arpeggiator(self):
        """Stop the arpeggiator"""
        self.arp_running = False
        self.log_status("🎶 Arpeggiator stopped")
        
    def run_arpeggiator(self):
        """Main arpeggiator loop"""
        while self.arp_running and self.arp_notes:
            try:
                # Calculate delay between notes based on BPM
                bpm = self.arp_speed.get()
                delay = 60.0 / (bpm * 4)  # 16th notes
                
                # Generate note sequence based on pattern
                sequence = self.generate_arp_sequence()
                
                for note in sequence:
                    if not self.arp_running or not self.arp_notes:
                        break
                        
                    # Play note (handle both simple keys and CTRL combinations for black keys)
                    key_mapping = self.action_map.get(note)
                    if key_mapping:
                        # Update spectrum for arp note start
                        self.update_note_spectrum(note, 80, True)  # Use velocity 80 for arp notes
                        
                        # Handle CTRL key combinations for black keys (sharps)
                        if isinstance(key_mapping, tuple):
                            if key_mapping[0] == 'ctrl':
                                self.send_ctrl_key(key_mapping[1], press=True)
                                time.sleep(delay * 0.8)  # Note duration
                                self.send_ctrl_key(key_mapping[1], press=False)
                                
                                note_name = self.get_note_name(note)
                                key_char = f"CTRL+{chr(key_mapping[1])}"
                                self.log_status(f"🎶♯ ARP: {note_name} → {key_char}")
                            elif key_mapping[0] == 'shift':
                                self.send_shift_key(key_mapping[1], press=True)
                                time.sleep(delay * 0.8)  # Note duration  
                                self.send_shift_key(key_mapping[1], press=False)
                                
                                note_name = self.get_note_name(note)
                                key_char = f"SHIFT+{chr(key_mapping[1])}"
                                self.log_status(f"🎶♯ ARP: {note_name} → {key_char}")
                        else:
                            # Handle simple key codes for white keys
                            self.send_key(key_mapping, press=True)
                            time.sleep(delay * 0.8)  # Note duration
                            self.send_key(key_mapping, press=False)
                            
                            note_name = self.get_note_name(note)
                            key_char = chr(key_mapping) if 32 <= key_mapping <= 126 else f"VK_{key_mapping}"
                            self.log_status(f"🎶 ARP: {note_name} → {key_char}")
                        
                        # Update spectrum for arp note end (after delay)
                        self.update_note_spectrum(note, 0, False)
                        
                    time.sleep(delay * 0.2)  # Gap between notes
                    
            except Exception as e:
                self.log_status(f"Arpeggiator error: {e}")
                break
                
    def generate_arp_sequence(self):
        """Generate arpeggiator note sequence"""
        if not self.arp_notes:
            return []
            
        base_notes = sorted(self.arp_notes)
        octave_range = self.arp_octaves.get()
        pattern = self.arp_pattern.get()
        
        # Extend notes across octaves
        extended_notes = []
        for octave in range(octave_range):
            for note in base_notes:
                extended_note = note + (octave * 12)
                if extended_note in self.action_map:  # Only use mappable notes
                    extended_notes.append(extended_note)
                    
        if not extended_notes:
            return base_notes
            
        # Apply pattern
        if pattern == "Up":
            return extended_notes
        elif pattern == "Down":
            return list(reversed(extended_notes))
        elif pattern == "Up-Down":
            return extended_notes + list(reversed(extended_notes[1:-1]))
        elif pattern == "Random":
            result = extended_notes.copy()
            random.shuffle(result)
            return result
        elif pattern == "As Played":
            return base_notes
        elif pattern in ["Pentatonic", "Diatonic", "Chromatic", "Mixolydian", "Dorian", "Lydian", "Blues Scale"]:
            return self.generate_scale_sequence(base_notes, octave_range, pattern)
        else:
            return extended_notes
    
    def generate_scale_sequence(self, base_notes, octave_range, scale_type):
        """Generate musical scale sequences based on root note"""
        if not base_notes:
            return []
        
        # Use the first (lowest) note as the root for scale generation
        root_note = base_notes[0]
        
        # Define scale intervals (semitones from root)
        scale_intervals = {
            "Pentatonic": [0, 2, 4, 7, 9],           # Major Pentatonic: C-D-E-G-A
            "Diatonic": [0, 2, 4, 5, 7, 9, 11],     # Major Scale: C-D-E-F-G-A-B
            "Chromatic": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],  # All 12 notes
            "Mixolydian": [0, 2, 4, 5, 7, 9, 10],   # Mixolydian Mode: C-D-E-F-G-A-Bb
            "Dorian": [0, 2, 3, 5, 7, 9, 10],       # Dorian Mode: C-D-Eb-F-G-A-Bb
            "Lydian": [0, 2, 4, 6, 7, 9, 11],       # Lydian Mode: C-D-E-F#-G-A-B
            "Blues Scale": [0, 3, 5, 6, 7, 10]       # Blues Scale: C-Eb-F-F#-G-Bb
        }
        
        intervals = scale_intervals.get(scale_type, [0, 2, 4, 7, 9])  # Default to pentatonic
        
        # Generate scale notes across octave range
        scale_notes = []
        for octave in range(octave_range):
            for interval in intervals:
                note = root_note + (octave * 12) + interval
                # Only add notes that exist in our action mapping
                if note in self.action_map:
                    scale_notes.append(note)
        
        # Remove duplicates and sort
        scale_notes = sorted(list(set(scale_notes)))
        
        return scale_notes
            
    def toggle_arpeggiator(self):
        """Toggle arpeggiator on/off"""
        if not self.arp_enabled.get():
            # Switching to normal mode
            self.stop_arpeggiator()
            self.arp_notes.clear()
            # Clear display and show normal mode message
            self.chord_display.config(state='normal')
            self.chord_display.delete(1.0, 'end')
            self.chord_display.insert(1.0, "Normal Mode: Raw MIDI output will appear here\nPlay notes to see MIDI → Key mapping")
            self.chord_display.config(state='disabled')
        else:
            # Switching to arp mode
            self.chord_display.config(state='normal')
            self.chord_display.delete(1.0, 'end')
            self.chord_display.insert(1.0, "Arpeggiator Mode: Hold notes to see chord\nPress multiple keys to create chords")
            self.chord_display.config(state='disabled')
            
    def find_lotro_window(self):
        """Find the LOTRO game window."""
        # Common LOTRO window titles - try exact matches first
        lotro_titles = [
            "The Lord of the Rings Online™",
            "The Lord of the Rings Online", 
            "LOTRO", 
            "Lord of the Rings Online"
        ]
        
        for title in lotro_titles:
            hwnd = windll.user32.FindWindowW(None, title)
            if hwnd:
                return hwnd
        
        # If no exact match, return 0 (will use global key events)
        return 0

    def send_ctrl_key(self, hex_code, press=True):
        """Send CTRL+key combination for sharps/flats"""
        VK_CONTROL = 0x11
        
        # First, ensure LOTRO is in focus
        lotro_hwnd = self.find_lotro_window()
        if lotro_hwnd:
            windll.user32.SetForegroundWindow(lotro_hwnd)
            windll.user32.SetActiveWindow(lotro_hwnd)
            time.sleep(0.002)  # Minimal delay for focus
        
        # Always reset modifiers first to prevent conflicts
        self.reset_all_modifiers()
        time.sleep(0.002)  # Small delay after reset
        
        if press:
            # Press CTRL first
            self.send_key(VK_CONTROL, press=True)
            time.sleep(0.001)  # Small delay between CTRL and key
            # Press the number key
            self.send_key(hex_code, press=True)
            time.sleep(0.001)  # Ensure key is registered
            # IMMEDIATELY release both to prevent sticking
            self.send_key(hex_code, press=False)
            time.sleep(0.001)
            self.send_key(VK_CONTROL, press=False)
        # For note_off, do nothing since we already released everything

    def send_shift_key(self, hex_code, press=True):
        """Send SHIFT+key combination for extended range"""
        VK_SHIFT = 0x10
        
        # First, ensure LOTRO is in focus
        lotro_hwnd = self.find_lotro_window()
        if lotro_hwnd:
            windll.user32.SetForegroundWindow(lotro_hwnd)
            windll.user32.SetActiveWindow(lotro_hwnd)
            time.sleep(0.002)  # Minimal delay for focus
        
        # Always reset modifiers first to prevent conflicts
        self.reset_all_modifiers()
        time.sleep(0.002)  # Small delay after reset
        
        if press:
            # Press SHIFT first
            self.send_key(VK_SHIFT, press=True)
            time.sleep(0.001)  # Small delay between SHIFT and key
            # Press the number key
            self.send_key(hex_code, press=True)
            time.sleep(0.001)  # Ensure key is registered
            # IMMEDIATELY release both to prevent sticking
            self.send_key(hex_code, press=False)
            time.sleep(0.001)
            self.send_key(VK_SHIFT, press=False)
        # For note_off, do nothing since we already released everything

    def reset_all_modifiers(self):
        """Force release all modifier keys to prevent sticking"""
        VK_SHIFT = 0x10
        VK_CONTROL = 0x11
        VK_ALT = 0x12
        
        # Force release all modifiers
        self.send_key(VK_SHIFT, press=False)
        self.send_key(VK_CONTROL, press=False)
        self.send_key(VK_ALT, press=False)

    def send_shift_ctrl_key(self, hex_code, press=True):
        """Send SHIFT+CTRL+key combination for higher octave sharps/flats - INCREASED TIMING FOR MAJOR 7TH"""
        VK_SHIFT = 0x10
        VK_CONTROL = 0x11
        
        # First, ensure LOTRO is in focus
        lotro_hwnd = self.find_lotro_window()
        if lotro_hwnd:
            windll.user32.SetForegroundWindow(lotro_hwnd)
            windll.user32.SetActiveWindow(lotro_hwnd)
            time.sleep(0.005)  # Increased delay for focus
        
        # Always reset modifiers first to prevent conflicts
        self.reset_all_modifiers()
        time.sleep(0.005)  # Increased delay after reset
        
        if press:
            # Press SHIFT first
            self.send_key(VK_SHIFT, press=True)
            time.sleep(0.005)  # Increased delay
            # Press CTRL second
            self.send_key(VK_CONTROL, press=True)
            time.sleep(0.005)  # Increased delay between modifiers and key
            # Press the number key
            self.send_key(hex_code, press=True)
            time.sleep(0.010)  # Much longer key registration time
            # IMMEDIATELY release everything to prevent sticking
            self.send_key(hex_code, press=False)
            time.sleep(0.003)
            self.send_key(VK_CONTROL, press=False)
            time.sleep(0.003)
            self.send_key(VK_SHIFT, press=False)
        # For note_off, do nothing since we already released everything

    def send_key(self, hex_code, press=True):
        """Send key ONLY to LOTRO window - prevents keys from going to other applications"""
        from ctypes import Structure, c_ulong, c_ushort, Union, byref, sizeof
        
        # Find LOTRO window - REQUIRED
        lotro_hwnd = self.find_lotro_window()
        if not lotro_hwnd:
            # No LOTRO window found - do NOT send keys globally
            return False
        
        action = "press" if press else "release"
        key_char = chr(hex_code) if 32 <= hex_code <= 126 else f"VK_{hex_code}"
        
        # ONLY use PostMessage to send directly to LOTRO window
        try:
            if press:
                WM_KEYDOWN = 0x0100
                WM_CHAR = 0x0102
            else:
                WM_KEYDOWN = 0x0101  # WM_KEYUP
                WM_CHAR = None
            
            scan_code = windll.user32.MapVirtualKeyW(hex_code, 0)
            lparam = (scan_code << 16) | (0xC0000001 if not press else 1)  # Set release flag for keyup
            
            result1 = windll.user32.PostMessageW(lotro_hwnd, WM_KEYDOWN, hex_code, lparam)
            if press and WM_CHAR:
                result2 = windll.user32.PostMessageW(lotro_hwnd, WM_CHAR, hex_code, lparam)
            else:
                result2 = True  # No WM_CHAR for key release
            
            return result1 and result2
            
        except Exception as e:
            self.log_status(f"Key send error: {e}")
            return False
            
    def get_note_name(self, note):
        """Convert MIDI note number to note name"""
        note_names = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
        octave = (note // 12) - 1
        return f"{note_names[note % 12]}{octave}"

    # Spectrum Analyzer Functions
    def start_spectrum_analyzer(self):
        """Start the spectrum analyzer update thread"""
        if not self.spectrum_running:
            self.spectrum_running = True
            self.spectrum_update_thread = threading.Thread(target=self.update_spectrum_display, daemon=True)
            self.spectrum_update_thread.start()
    
    def stop_spectrum_analyzer(self):
        """Stop the spectrum analyzer"""
        self.spectrum_running = False
    
    def toggle_spectrum_analyzer(self):
        """Toggle spectrum analyzer on/off"""
        if self.spectrum_enabled.get():
            self.start_spectrum_analyzer()
        else:
            self.stop_spectrum_analyzer()
            # Clear the canvas
            if self.spectrum_canvas:
                self.spectrum_canvas.delete("all")
    
    def update_note_spectrum(self, note, velocity, note_on=True):
        """Update spectrum data when notes are played"""
        if not self.spectrum_enabled.get() or note < 21 or note > 108:
            return
        
        # Map MIDI note (21-108) to spectrum index (0-87)
        spectrum_index = note - 21
        
        if note_on and velocity > 0:
            # Note on - set volume based on velocity
            normalized_velocity = velocity / 127.0
            self.spectrum_data[spectrum_index] = normalized_velocity * self.spectrum_sensitivity.get()
        else:
            # Note off - gradually decay the volume
            current_level = self.spectrum_data[spectrum_index]
            self.spectrum_data[spectrum_index] = max(0.0, current_level * 0.7)  # Decay factor
    
    def update_spectrum_display(self):
        """Update the spectrum display in real-time"""
        while self.spectrum_running:
            try:
                if self.spectrum_canvas and self.spectrum_enabled.get():
                    # Clear canvas
                    self.spectrum_canvas.delete("all")
                    
                    canvas_width = self.spectrum_canvas.winfo_width()
                    canvas_height = self.spectrum_canvas.winfo_height()
                    
                    if canvas_width > 1 and canvas_height > 1:
                        # Calculate bar dimensions
                        num_bars = len(self.spectrum_data)
                        bar_width = max(1, (canvas_width - 20) / num_bars)
                        max_height = canvas_height - 40
                        
                        # Draw spectrum bars
                        for i, level in enumerate(self.spectrum_data):
                            if level > 0.01:  # Only draw if there's significant level
                                x = 10 + (i * bar_width)
                                bar_height = min(max_height, level * max_height)
                                y1 = canvas_height - 20
                                y2 = y1 - bar_height
                                
                                # Color based on intensity (blue -> green -> yellow -> red)
                                if level < 0.25:
                                    color = f"#{int(0):02x}{int(level*4*255):02x}{int(255):02x}"  # Blue to Cyan
                                elif level < 0.5:
                                    color = f"#{int(0):02x}{int(255):02x}{int(255-(level-0.25)*4*255):02x}"  # Cyan to Green
                                elif level < 0.75:
                                    color = f"#{int((level-0.5)*4*255):02x}{int(255):02x}{int(0):02x}"  # Green to Yellow
                                else:
                                    color = f"#{int(255):02x}{int(255-(level-0.75)*4*255):02x}{int(0):02x}"  # Yellow to Red
                                
                                # Draw the bar
                                self.spectrum_canvas.create_rectangle(x, y1, x + bar_width - 1, y2, 
                                                                    fill=color, outline=color)
                                
                                # Add note label for active notes
                                if level > 0.1:
                                    note_num = i + 21
                                    note_name = self.get_note_name(note_num)
                                    self.spectrum_canvas.create_text(x + bar_width/2, y1 + 10, 
                                                                   text=note_name, fill='white', 
                                                                   font=('Arial', 6))
                        
                        # Draw frequency labels
                        self.spectrum_canvas.create_text(10, 10, text="A0", fill='#DAA520', 
                                                       font=('Arial', 8), anchor='w')
                        self.spectrum_canvas.create_text(canvas_width - 10, 10, text="C8", fill='#DAA520', 
                                                       font=('Arial', 8), anchor='e')
                        self.spectrum_canvas.create_text(canvas_width/2, 10, text="C4 (Middle C)", fill='#DAA520', 
                                                       font=('Arial', 8), anchor='center')
                
                # Decay all spectrum levels gradually
                for i in range(len(self.spectrum_data)):
                    if self.spectrum_data[i] > 0:
                        self.spectrum_data[i] = max(0.0, self.spectrum_data[i] * 0.95)  # Gradual decay
                
                time.sleep(0.05)  # Update at 20 FPS
                
            except Exception as e:
                # Silently continue if there are any display errors
                time.sleep(0.1)

    # MIDI Import & Playback Functions
    def load_midi_file(self):
        """Load a MIDI file for playback"""
        from tkinter import filedialog
        
        filename = filedialog.askopenfilename(
            filetypes=[("MIDI files", "*.mid *.midi"), ("All files", "*.*")],
            title="Load MIDI File"
        )
        
        if filename:
            try:
                self.loaded_midi = mido.MidiFile(filename)
                self.loaded_midi_file_path = filename  # Store for audio playback
                self.midi_filename_label.config(text=f"Loaded: {filename.split('/')[-1]}")
                self.midi_play_btn.config(state='normal')
                
                # Update title bar with filename
                self.update_midi_title(filename)
                
                # Display MIDI file info
                self.display_midi_info()
                self.log_status(f"🎵 MIDI file loaded: {filename.split('/')[-1]}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load MIDI file:\n{e}")
                self.log_status(f"❌ Error loading MIDI: {e}")

    def display_midi_info(self):
        """Display information about the loaded MIDI file"""
        if not self.loaded_midi:
            return
            
        self.midi_info_text.config(state='normal')
        self.midi_info_text.delete(1.0, 'end')
        
        # Analyze MIDI file
        total_time = self.loaded_midi.length
        track_count = len(self.loaded_midi.tracks)
        
        info_text = f"MIDI File Information:\n"
        info_text += f"Duration: {total_time:.1f} seconds\n"
        info_text += f"Tracks: {track_count}\n"
        info_text += f"Ticks per beat: {self.loaded_midi.ticks_per_beat}\n\n"
        
        # Analyze tracks for note events
        for i, track in enumerate(self.loaded_midi.tracks):
            note_count = sum(1 for msg in track if msg.type == 'note_on')
            if note_count > 0:
                info_text += f"Track {i}: {note_count} notes\n"
        
        self.midi_info_text.insert('end', info_text)
        self.midi_info_text.config(state='disabled')

    def convert_midi_to_abc(self):
        """Convert loaded MIDI file to ABC notation"""
        if not self.loaded_midi:
            messagebox.showwarning("Warning", "Please load a MIDI file first!")
            return
            
        try:
            # Clear current ABC content
            self.abc_text.config(state='normal')
            self.abc_text.delete(1.0, 'end')
            
            # Add ABC header
            self.abc_text.insert('end', "% MIDI Import - Converted to ABC\n")
            self.abc_text.insert('end', "X: 1\n")
            self.abc_text.insert('end', "T: MIDI Import\n")
            self.abc_text.insert('end', "M: 4/4\n")
            self.abc_text.insert('end', "L: 1/8\n")
            self.abc_text.insert('end', "Q: 120\n")
            self.abc_text.insert('end', "K: C\n")
            self.abc_text.insert('end', "% Notes:\n")
            
            # Convert MIDI notes to ABC
            note_count = 0
            for track in self.loaded_midi.tracks:
                for msg in track:
                    if msg.type == 'note_on' and msg.velocity > 0:
                        abc_note = self.midi_to_abc_note(msg.note)
                        if abc_note and note_count < 200:  # Limit to prevent overflow
                            self.abc_text.insert('end', f"{abc_note} ")
                            note_count += 1
                            
                            # Add bar lines every 8 notes
                            if note_count % 8 == 0:
                                self.abc_text.insert('end', "|\n")
            
            self.abc_text.insert('end', "|\n% End of MIDI conversion")
            self.abc_text.config(state='disabled')
            self.log_status(f"🎼 MIDI converted to ABC ({note_count} notes)")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to convert MIDI:\n{e}")
            self.log_status(f"❌ MIDI conversion error: {e}")

    def play_midi_file(self):
        """Play the loaded MIDI file through LOTRO and Windows audio"""
        if not self.loaded_midi:
            messagebox.showwarning("Warning", "Please load a MIDI file first!")
            return
            
        if self.midi_playing:
            return
            
        # Try to play audio through Windows
        try:
            import pygame
            pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=1024)
            
            # Load and play the MIDI file for audio
            if hasattr(self, 'loaded_midi_file_path'):
                try:
                    pygame.mixer.music.load(self.loaded_midi_file_path)
                    pygame.mixer.music.play()
                    self.log_status("🔊 MIDI audio playback started")
                except:
                    self.log_status("⚠️ Audio playback not available, using key simulation only")
            
        except ImportError:
            self.log_status("⚠️ pygame not installed - install with: pip install pygame")
        except Exception as e:
            self.log_status(f"⚠️ Audio error: {e}")
            
        # Start LOTRO key simulation playback in separate thread
        self.midi_playing = True
        self.midi_play_btn.config(state='disabled')
        self.midi_stop_btn.config(state='normal')
        
        self.midi_playback_thread = threading.Thread(target=self.run_midi_playback, daemon=True)
        self.midi_playback_thread.start()
        self.log_status("🎵 MIDI playback started")

    def run_midi_playback(self):
        """Main MIDI playback loop"""
        try:
            speed_multiplier = self.midi_speed.get()
            
            for track in self.loaded_midi.tracks:
                if not self.midi_playing:
                    break
                    
                current_time = 0
                
                for msg in track:
                    if not self.midi_playing:
                        break
                        
                    # Handle timing
                    if hasattr(msg, 'time'):
                        wait_time = mido.tick2second(msg.time, self.loaded_midi.ticks_per_beat, 500000) / speed_multiplier
                        if wait_time > 0:
                            time.sleep(wait_time)
                    
                    # Play note events
                    if msg.type == 'note_on' and msg.velocity > 0:
                        self.handle_note_on(msg.note)
                    elif msg.type == 'note_off' or (msg.type == 'note_on' and msg.velocity == 0):
                        self.handle_note_off(msg.note)
                        
        except Exception as e:
            self.log_status(f"❌ MIDI playback error: {e}")
        finally:
            self.stop_midi_playback()

    def stop_midi_playback(self):
        """Stop MIDI file playback"""
        self.midi_playing = False
        
        # Stop pygame audio if it's playing
        try:
            import pygame
            if pygame.mixer.get_init():
                pygame.mixer.music.stop()
                self.log_status("🔇 Audio playback stopped")
        except:
            pass  # pygame not available or not initialized
        
        self.midi_play_btn.config(state='normal')
        self.midi_stop_btn.config(state='disabled')
        self.log_status("⏹️ MIDI playback stopped")

    def toggle_abc_recording(self):
        """Toggle ABC notation recording"""
        if self.abc_recording.get():
            self.stop_abc_recording()
        else:
            self.start_abc_recording()

    def start_abc_recording(self):
        """Start recording ABC notation"""
        self.abc_notes = []
        self.abc_start_time = time.time()
        self.abc_recording.set(True)
        
        # Update button appearance
        self.abc_record_btn.config(text="⏹️ Stop ABC     ", bg='#FF0000', fg='#FFFFFF')
        
        self.abc_text.config(state='normal')
        self.abc_text.delete(1.0, 'end')
        self.abc_text.insert('end', "% LOTRO ABC Export - Recording...\n")
        self.abc_text.insert('end', "X: 1\n")
        self.abc_text.insert('end', "T: MIDI Recording\n")
        self.abc_text.insert('end', f"M: 4/4\n")
        self.abc_text.insert('end', f"L: 1/8\n")
        self.abc_text.insert('end', f"Q: {self.abc_tempo}\n")
        self.abc_text.insert('end', "K: C\n")
        self.abc_text.insert('end', "% Notes:\n")
        self.abc_text.config(state='disabled')
        self.log_status("🎼 ABC recording started")

    def stop_abc_recording(self):
        """Stop recording ABC notation"""
        self.abc_recording.set(False)
        
        # Update button appearance back to normal
        self.abc_record_btn.config(text="🎼 Record ABC", bg='#FFFFFF', fg='#FF0000')
        
        # Always finalize, even if no notes were recorded
        self.finalize_abc_notation()
        note_count = len(self.abc_notes)
        self.log_status(f"🎼 ABC recording stopped ({note_count} notes recorded)")

    def record_abc_note(self, midi_note, velocity, note_on=True):
        """Record a note for ABC notation with duration tracking"""
        if not self.abc_recording.get():
            return
            
        current_time = time.time()
        if self.abc_start_time is None:
            self.abc_start_time = current_time
            
        # Convert MIDI note to ABC notation
        abc_note = self.midi_to_abc_note(midi_note)
        if not abc_note:
            return
            
        # Initialize note tracking dictionary if needed
        if not hasattr(self, 'active_abc_notes'):
            self.active_abc_notes = {}
            
        if note_on:
            # Note started - record start time
            self.active_abc_notes[midi_note] = current_time
            
        else:
            # Note ended - calculate duration and add to ABC
            if midi_note in self.active_abc_notes:
                start_time = self.active_abc_notes[midi_note]
                duration_seconds = current_time - start_time
                del self.active_abc_notes[midi_note]
                
                # Convert duration to ABC notation
                # Base quarter note = 0.6 seconds (reasonable tempo)
                base_quarter_note = 0.6
                duration_ratio = duration_seconds / base_quarter_note
                
                # Convert to ABC duration notation
                if duration_ratio >= 3.5:
                    abc_duration = "4"    # Whole note
                elif duration_ratio >= 1.75:
                    abc_duration = "2"    # Half note  
                elif duration_ratio >= 0.75:
                    abc_duration = ""     # Quarter note (default, no number)
                elif duration_ratio >= 0.375:
                    abc_duration = "/2"   # Eighth note
                else:
                    abc_duration = "/4"   # Sixteenth note
                
                # Update display in real-time with duration
                note_with_duration = f"{abc_note}{abc_duration}"
                self.update_abc_display(note_with_duration)

    def midi_to_abc_note(self, midi_note):
        """Convert MIDI note number to ABC notation"""
        # ABC notation mapping for LOTRO range
        note_names = ['C', '^C', 'D', '^D', 'E', 'F', '^F', 'G', '^G', 'A', '^A', 'B']
        
        if midi_note < 12 or midi_note > 127:
            return None
            
        octave = (midi_note // 12) - 1
        note_index = midi_note % 12
        base_note = note_names[note_index]
        
        # ABC octave notation
        if octave < 4:
            # Lower octaves use uppercase with commas
            octave_marker = ',' * (4 - octave) if octave < 4 else ''
            return f"{base_note}{octave_marker}"
        elif octave == 4:
            # Middle octave uses uppercase
            return base_note
        else:
            # Higher octaves use lowercase with apostrophes
            octave_marker = "'" * (octave - 4) if octave > 4 else ''
            return f"{base_note.lower()}{octave_marker}"

    def update_abc_display(self, abc_note):
        """Update the ABC display with new note"""
        self.abc_text.config(state='normal')
        self.abc_text.insert('end', f"{abc_note} ")
        
        # Add line breaks every 16 notes for readability
        content = self.abc_text.get(1.0, 'end')
        note_count = content.count(' ') - content.count('\n') * 2  # Rough note count
        if note_count > 0 and note_count % 16 == 0:
            self.abc_text.insert('end', "|\n")  # Bar line and new line
            
        self.abc_text.see('end')
        self.abc_text.config(state='disabled')

    def finalize_abc_notation(self):
        """Finalize the ABC notation when recording stops"""
        self.abc_text.config(state='normal')
        
        # Replace "Recording..." with "Complete"
        content = self.abc_text.get(1.0, 'end')
        if "Recording..." in content:
            updated_content = content.replace("Recording...", "Complete")
            self.abc_text.delete(1.0, 'end')
            self.abc_text.insert(1.0, updated_content)
        
        # Add final bar and end comment
        self.abc_text.insert('end', "|\n% End of recording")
        self.abc_text.config(state='disabled')

    def save_abc_file(self):
        """Save ABC notation to file"""
        from tkinter import filedialog
        
        content = self.abc_text.get(1.0, 'end').strip()
        # Check if there's actual ABC content (more than just headers)
        lines = content.split('\n')
        has_notes = any(line.strip() and not line.startswith('%') and not line.startswith(('X:', 'T:', 'M:', 'L:', 'Q:', 'K:')) for line in lines)
        
        if not content or not has_notes:
            messagebox.showwarning("Warning", "No ABC notation to save! Make sure you:\n1. Enable ABC recording\n2. Play some notes\n3. Stop recording")
            return
            
        filename = filedialog.asksaveasfilename(
            defaultextension=".abc",
            filetypes=[("ABC files", "*.abc"), ("Text files", "*.txt"), ("All files", "*.*")],
            title="Save ABC Notation"
        )
        
        if filename:
            try:
                with open(filename, 'w') as f:
                    f.write(content)
                
                # Update title bar with filename
                self.update_abc_title(filename)
                
                self.log_status(f"📁 ABC file saved: {filename}")
                messagebox.showinfo("Success", f"ABC file saved successfully!\n{filename}")
            except Exception as e:
                self.log_status(f"❌ Error saving ABC file: {e}")
                messagebox.showerror("Error", f"Failed to save ABC file:\n{e}")

    def load_abc_file(self):
        """Load ABC notation from file"""
        from tkinter import filedialog
        
        filename = filedialog.askopenfilename(
            filetypes=[("ABC files", "*.abc"), ("Text files", "*.txt"), ("All files", "*.*")],
            title="Load ABC Notation File"
        )
        
        if filename:
            try:
                with open(filename, 'r') as f:
                    content = f.read()
                
                # Clear current content and load new content
                self.abc_text.config(state='normal')
                self.abc_text.delete(1.0, 'end')
                self.abc_text.insert(1.0, content)
                self.abc_text.config(state='disabled')
                
                # Update title bar with filename
                self.update_abc_title(filename)
                
                self.log_status(f"📂 ABC file loaded: {filename}")
                # messagebox.showinfo("Success", f"ABC file loaded successfully!\n{filename}")
                
            except Exception as e:
                self.log_status(f"❌ Error loading ABC file: {e}")
                messagebox.showerror("Error", f"Failed to load ABC file:\n{e}")

    def export_abc_to_midi(self):
        """Export ABC notation to MIDI file"""
        from tkinter import filedialog
        
        # Get ABC content
        content = self.abc_text.get(1.0, 'end').strip()
        if not content or content == "":
            messagebox.showwarning("Warning", "No ABC content to export! Please load or record ABC notation first.")
            return
            
        # Choose save location
        filename = filedialog.asksaveasfilename(
            defaultextension=".mid",
            filetypes=[("MIDI files", "*.mid"), ("All files", "*.*")],
            title="Export ABC to MIDI File"
        )
        
        if filename:
            try:
                # Parse ABC content and convert to MIDI
                self.convert_abc_to_midi(content, filename)
                
                self.log_status(f"🎹 ABC exported to MIDI: {filename}")
                messagebox.showinfo("Success", f"ABC notation exported to MIDI successfully!\n{filename}")
                
            except Exception as e:
                self.log_status(f"❌ Error exporting MIDI: {e}")
                messagebox.showerror("Error", f"Failed to export MIDI file:\n{e}")
    
    def convert_abc_to_midi(self, abc_content, filename):
        """Convert ABC notation content to MIDI file"""
        import mido
        from mido import MidiFile, MidiTrack, Message
        
        # Create new MIDI file with single track
        midi_file = MidiFile()
        track = MidiTrack()
        midi_file.tracks.append(track)
        
        # Add program change for Piano (General MIDI)
        track.append(Message('program_change', channel=0, program=0, time=0))  # Piano 1
        
        # Parse ABC content to extract notes
        lines = abc_content.split('\n')
        notes_line = ""
        
        # Find the actual music notes (same logic as playback)
        for line in lines:
            line = line.strip()
            if (not line.startswith(('X:', 'T:', 'M:', 'L:', 'Q:', 'K:', '%', 'P:', 'C:', 'A:', 'B:', 'H:', 'I:', 'N:', 'O:', 'R:', 'S:', 'U:', 'V:', 'W:', 'w:', 'Z:')) and 
                line and len(line) > 0):
                # Keep ABC notation symbols
                cleaned_line = ''.join(c for c in line if c.isalpha() or c in '^_ ,\'/2345678')
                notes_line += cleaned_line + " "
        
        if not notes_line.strip():
            raise ValueError("No playable notes found in ABC content")
        
        self.log_status(f"🎵 Converting ABC to MIDI: '{notes_line.strip()}'")
        
        # Parse notes and convert to MIDI events
        notes_string = notes_line.strip()
        base_note_duration = 480  # MIDI ticks per quarter note
        current_time = 0
        
        i = 0
        while i < len(notes_string):
            char = notes_string[i]
            original_note = ""
            note_duration = base_note_duration  # Default quarter note
            
            # Check for ABC sharp/flat modifiers BEFORE the note
            accidental = ""
            if char == '^':
                accidental = "^"
                original_note += "^"
                i += 1
                if i < len(notes_string):
                    char = notes_string[i]
            elif char == '_':
                accidental = "_"
                original_note += "_"
                i += 1
                if i < len(notes_string):
                    char = notes_string[i]
            
            # Process note letter
            if char.upper() in 'CDEFGAB':
                note_name = char.upper()
                original_note += char
                i += 1
                
                # Skip octave markers but track them
                while i < len(notes_string) and notes_string[i] in "',":
                    original_note += notes_string[i]
                    i += 1
                
                # Map note to MIDI (same logic as playback)
                if char.isupper():
                    if ',' in original_note:
                        # C3 octave
                        base_midi = {'C': 48, 'D': 50, 'E': 52, 'F': 53, 'G': 55, 'A': 57, 'B': 59}
                    else:
                        # C4 octave  
                        base_midi = {'C': 60, 'D': 62, 'E': 64, 'F': 65, 'G': 67, 'A': 69, 'B': 71}
                else:
                    # C5 octave
                    base_midi = {'C': 72, 'D': 74, 'E': 76, 'F': 77, 'G': 79, 'A': 81, 'B': 83}
                
                midi_note = base_midi.get(note_name)
                if not midi_note:
                    continue
                
                # Apply accidental
                if accidental == "^":
                    midi_note += 1  # Sharp
                elif accidental == "_":
                    midi_note -= 1  # Flat
                
                # Parse duration modifiers
                duration_str = ""
                while i < len(notes_string) and (notes_string[i].isdigit() or notes_string[i] in '/.'):
                    duration_str += notes_string[i]
                    i += 1
                
                # Calculate MIDI duration
                if duration_str:
                    try:
                        if '/' in duration_str:
                            if duration_str.startswith('/'):
                                divisor = int(duration_str[1:])
                                note_duration = base_note_duration // divisor
                            else:
                                parts = duration_str.split('/')
                                numerator = int(parts[0]) if parts[0] else 1
                                denominator = int(parts[1]) if len(parts) > 1 else 1
                                note_duration = base_note_duration * numerator // denominator
                        else:
                            multiplier = int(duration_str)
                            note_duration = base_note_duration * multiplier
                    except ValueError:
                        note_duration = base_note_duration
                
                # Add MIDI note on/off events
                track.append(Message('note_on', channel=0, note=midi_note, velocity=80, time=current_time))
                track.append(Message('note_off', channel=0, note=midi_note, velocity=0, time=note_duration))
                
                current_time = 0  # Time is relative to previous event
                
            else:
                # Handle spaces and other characters (rests)
                if char == ' ':
                    current_time += base_note_duration // 2  # Rest duration
                i += 1
        
        # Save MIDI file
        midi_file.save(filename)

    def clear_abc(self):
        """Clear the ABC notation display"""
        self.abc_text.config(state='normal')
        self.abc_text.delete(1.0, 'end')
        self.abc_text.config(state='disabled')
        self.abc_notes = []
        
        # Clear filename from title
        self.update_abc_title(None)
        
        self.log_status("🗑️ ABC notation cleared")

    def play_abc_content(self):
        """Play ABC notation content through LOTRO key simulation"""
        content = self.abc_text.get(1.0, 'end').strip()
        
        if not content or content == "":
            # This shouldn't happen if called from countdown, but just in case
            messagebox.showwarning("Warning", "No ABC content to play! Please load an ABC file or record some notes first.")
            # Reset button state
            self.abc_play_btn.config(state='normal', text="▶️ Toggle Play ABC", bg='#32CD32')
            return
        
        # Parse ABC content and convert to key presses
        try:
            # Set playing state and update button
            self.abc_playing = True
            self.abc_play_btn.config(state='normal', text="⏹️ Stop ABC", bg='#FF6B6B')
            
            # Extract notes from ABC notation (improved parser)
            lines = content.split('\n')
            notes_line = ""
            
            # Debug: Show what we're parsing
            self.log_status(f"🔍 ABC Content Preview: {content[:200]}...")
            
            # Find the actual music notes (after the header)
            for line in lines:
                line = line.strip()
                # Skip header lines and comments, but include lines with bar markers
                if (not line.startswith(('X:', 'T:', 'M:', 'L:', 'Q:', 'K:', '%', 'P:', 'C:', 'A:', 'B:', 'H:', 'I:', 'N:', 'O:', 'R:', 'S:', 'U:', 'V:', 'W:', 'w:', 'Z:')) and 
                    line and len(line) > 0):
                    # Remove bar markers and other symbols but keep the notes and ABC accidentals
                    cleaned_line = ''.join(c for c in line if c.isalpha() or c in '^_ ,\'/2345678')
                    notes_line += cleaned_line + " "
            
            # Debug: Show extracted notes
            self.log_status(f"🎵 Extracted notes: '{notes_line.strip()}'")
            
            if not notes_line.strip():
                self.stop_abc_playback()
                messagebox.showinfo("Info", "No playable notes found in ABC content.")
                return
            
            # Start playback in a separate thread
            self.abc_playback_thread = threading.Thread(target=self.play_abc_notes, args=[notes_line.strip()], daemon=True)
            self.abc_playback_thread.start()
            
            self.log_status("🎵 Playing ABC notation...")
            
        except Exception as e:
            self.stop_abc_playback()
            self.log_status(f"❌ Error playing ABC: {e}")
            messagebox.showerror("Error", f"Failed to play ABC notation:\n{e}")

    def play_abc_notes(self, notes_string):
        """Play parsed ABC notes with proper duration and sustain handling"""
        try:
            # ABC note parsing with proper octave handling
            
            # Base timing values (in seconds)
            base_note_duration = 0.4  # Quarter note duration
            key_press_duration = 0.05  # How long to hold the key down
            
            # Debug: Show the notes string we're processing
            self.log_status(f"🎶 Processing ABC notes: '{notes_string}'")
            
            # Show character by character for debugging
            char_debug = " ".join(f"'{c}'" for c in notes_string[:50])  # First 50 chars
            self.log_status(f"🔍 Characters: {char_debug}{'...' if len(notes_string) > 50 else ''}")
            
            note_count = 0
            # Parse notes and play them
            i = 0
            while i < len(notes_string) and self.abc_playing:
                char = notes_string[i]
                original_note = ""
                note_duration = base_note_duration  # Default quarter note
                
                # Check for ABC sharp/flat modifiers BEFORE the note
                accidental = ""
                if char == '^':
                    # Sharp in ABC notation
                    accidental = "^"
                    original_note += "^"
                    i += 1
                    if i < len(notes_string):
                        char = notes_string[i]  # Get the actual note
                elif char == '_':
                    # Flat in ABC notation  
                    accidental = "_"
                    original_note += "_"
                    i += 1
                    if i < len(notes_string):
                        char = notes_string[i]  # Get the actual note
                
                # Now process the note letter
                if char.upper() in 'CDEFGAB':
                    # Convert ABC note to MIDI, considering octave context
                    note_name = char.upper()
                    original_note += char
                    i += 1
                    
                    # Skip octave markers (commas and apostrophes) but track them
                    while i < len(notes_string) and notes_string[i] in "',":
                        original_note += notes_string[i]
                        i += 1
                    
                    # Map note to MIDI based on case and octave markers (ABC convention)
                    if char.isupper():
                        if ',' in original_note:
                            # Uppercase with comma = lower octave (C3 = 48) 
                            base_midi = {'C': 48, 'D': 50, 'E': 52, 'F': 53, 'G': 55, 'A': 57, 'B': 59}
                        else:
                            # Uppercase without comma = middle octave (C4 = 60)
                            base_midi = {'C': 60, 'D': 62, 'E': 64, 'F': 65, 'G': 67, 'A': 69, 'B': 71}
                    else:
                        # Lowercase = higher octave (c5 = 72)  
                        base_midi = {'C': 72, 'D': 74, 'E': 76, 'F': 77, 'G': 79, 'A': 81, 'B': 83}
                    
                    midi_note = base_midi.get(note_name)
                    if not midi_note:
                        continue
                    
                    # Apply accidental
                    if accidental == "^":
                        midi_note += 1  # Sharp
                    elif accidental == "_":
                        midi_note -= 1  # Flat
                    
                    # Parse duration modifiers
                    duration_str = ""
                    while i < len(notes_string) and (notes_string[i].isdigit() or notes_string[i] in '/.'):
                        duration_str += notes_string[i]
                        i += 1
                    
                    # Calculate note duration from ABC notation
                    if duration_str:
                        try:
                            if '/' in duration_str:
                                # Handle fractions like /2, /4, 3/2, etc.
                                if duration_str.startswith('/'):
                                    # /2 = half duration, /4 = quarter duration
                                    divisor = int(duration_str[1:])
                                    note_duration = base_note_duration / divisor
                                else:
                                    # 3/2 = 1.5x duration
                                    parts = duration_str.split('/')
                                    numerator = int(parts[0]) if parts[0] else 1
                                    denominator = int(parts[1]) if len(parts) > 1 else 1
                                    note_duration = base_note_duration * (numerator / denominator)
                            else:
                                # Simple multiplier like 2, 3, 4
                                multiplier = int(duration_str)
                                note_duration = base_note_duration * multiplier
                        except ValueError:
                            # If parsing fails, use default duration
                            note_duration = base_note_duration
                    
                    # Debug: Show each note being played with duration
                    duration_info = f" (dur: {note_duration:.2f}s)" if duration_str else ""
                    self.log_status(f"🎵 Playing note: {original_note}{duration_str} -> MIDI {midi_note}{duration_info}")
                    note_count += 1
                    
                    # Convert MIDI note to key mapping
                    key_mapping = self.action_map.get(midi_note)
                    if key_mapping:
                        # Start key press
                        key_pressed = False
                        if isinstance(key_mapping, tuple):
                            if key_mapping[0] == 'ctrl':
                                self.send_ctrl_key(key_mapping[1], press=True)
                                key_pressed = True
                            elif key_mapping[0] == 'shift':
                                self.send_shift_key(key_mapping[1], press=True)
                                key_pressed = True
                        else:
                            self.send_key(key_mapping, press=True)
                            key_pressed = True
                        
                        if key_pressed:
                            # Hold the key for the appropriate duration (sustain)
                            sustain_time = min(note_duration - 0.02, note_duration * 0.9)  # Leave small gap
                            time.sleep(max(sustain_time, key_press_duration))
                            
                            # Release key
                            if isinstance(key_mapping, tuple):
                                if key_mapping[0] == 'ctrl':
                                    self.send_ctrl_key(key_mapping[1], press=False)
                                elif key_mapping[0] == 'shift':
                                    self.send_shift_key(key_mapping[1], press=False)
                                elif key_mapping[0] == 'alt':
                                    self.send_alt_key(key_mapping[1], press=False)
                                elif key_mapping[0] == 'shift+ctrl':
                                    self.send_shift_ctrl_key(key_mapping[1], press=False)
                                else:
                                    self.send_key(key_mapping[1], press=False)
                            else:
                                self.send_key(key_mapping, press=False)
                            
                            # Small gap between notes for articulation
                            gap_time = note_duration - sustain_time
                            if gap_time > 0:
                                time.sleep(gap_time)
                    else:
                        self.log_status(f"⚠️ No key mapping for MIDI {midi_note}")
                        # Still wait for the note duration even if we can't play it
                        time.sleep(note_duration)
                else:
                    # Handle spaces and other characters (rests)
                    if char == ' ':
                        time.sleep(base_note_duration * 0.5)  # Rest duration
                    i += 1
            
            self.log_status(f"✅ Finished playing {note_count} notes")
            
        except Exception as e:
            self.log_status(f"❌ Error during ABC playback: {e}")
        finally:
            # Always reset the button when playback finishes
            if self.abc_playing:
                self.stop_abc_playback()

    def toggle_abc_playback(self):
        """Toggle ABC playback on/off"""
        if self.abc_playing:
            self.stop_abc_playback()
        else:
            # Start countdown in separate thread before playing ABC
            countdown_thread = threading.Thread(target=self.countdown_and_play_abc, daemon=True)
            countdown_thread.start()
    
    def countdown_and_play_abc(self):
        """Countdown before starting ABC playback"""
        try:
            # Check if there's ABC content BEFORE starting countdown
            content = self.abc_text.get(1.0, 'end').strip()
            if not content or content == "":
                messagebox.showwarning("Warning", "No ABC content to play! Please load an ABC file or record some notes first.")
                # Don't disable button, just return
                return
            
            # Disable button during countdown
            self.abc_play_btn.config(state='disabled', text="Starting...", bg='#ff9800')
            
            # 3-second countdown with visual display
            for i in range(3, 0, -1):
                self.countdown_label.config(text=f"⏰ Starting ABC in {i}...\n🎮 Click into LOTRO now!")
                self.log_status(f"🕐 ABC Starting in {i} seconds... (Click into LOTRO now!)")
                self.root.update_idletasks()
                time.sleep(1)
                
            # Final ready message
            self.countdown_label.config(text="🎯 READY! 🎵", fg='#4CAF50')
            self.log_status("🎯 ABC Playback Active - Ready to play!")
            self.root.update_idletasks()
            time.sleep(0.5)
            
            # Clear countdown display
            self.countdown_label.config(text="")
            
            # Now start ABC playback
            self.play_abc_content()
            
        except Exception as e:
            self.log_status(f"✗ Failed to start ABC playback: {e}")
            self.abc_play_btn.config(state='normal', text="▶️ Toggle Play ABC", bg='#32CD32')
            self.countdown_label.config(text="")

    def stop_abc_playback(self):
        """Stop ABC playback"""
        self.abc_playing = False
        self.abc_play_btn.config(state='normal', text="▶️ Toggle Play ABC", bg='#32CD32')
        self.log_status("⏹️ ABC playback stopped")

def main():
    root = tk.Tk()
    app = MIDIControllerGUI(root)
    # Note: Window close handler is set up in the MIDIControllerGUI.__init__
    root.mainloop()

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n🔄 Application interrupted by user")
    except Exception as e:
        print(f"❌ Application error: {e}")
    finally:
        print("🔚 Application terminated")