import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from pythonosc import dispatcher, osc_server, udp_client
import mido
from mido import MidiFile
import threading
import socket
import json
import os
import re
import time
import asyncio
import random
import queue
from datetime import datetime, timedelta

# --------------------- Tooltip Class Definition --------------------- #
class Tooltip:
    """
    Creates a tooltip for a given widget as the mouse hovers over it.
    """
    def __init__(self, widget, text='widget info'):
        self.widget = widget
        self.text = text
        self.tooltip_window = None
        self.widget.bind("<Enter>", self.show_tooltip)
        self.widget.bind("<Leave>", self.hide_tooltip)

    def show_tooltip(self, event=None):
        if self.tooltip_window or not self.text:
            return
        # Create a new Toplevel window
        self.tooltip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)  # Remove window decorations
        tw.wm_geometry(f"+{self.widget.winfo_rootx()+20}+{self.widget.winfo_rooty()+20}")
        # Create a label inside the Toplevel
        label = tk.Label(tw, text=self.text, justify='left',
                         background="#333333", foreground="#FFFFFF",
                         relief='solid', borderwidth=1,
                         font=("tahoma", "8", "normal"))
        label.pack(ipadx=1)

    def hide_tooltip(self, event=None):
        if self.tooltip_window:
            self.tooltip_window.destroy()
        self.tooltip_window = None


# ----------------------- OSCMIDIApp Class ---------------------------- #
class OSCMIDIApp:
    CONFIG_FILE = "config.json"
    MAX_LOG_MESSAGES = 100  # Increased log capacity for better tracking

    def __init__(self, master):
        self.master = master
        self.master.title("OSC2MIDI - Live Edition (Dark)")

        # --- Dark theme (ttk.Style) ---
        style = ttk.Style(self.master)
        style.theme_use('clam')  # Use 'clam' for better styling control
        style.configure('.', background='#2B2B2B', foreground='#FFFFFF', bordercolor='#2B2B2B')
        style.configure('TFrame', background='#2B2B2B')
        style.configure('TLabel', background='#2B2B2B', foreground='#FFFFFF')
        style.configure('TButton', background='#3A3A3A', foreground='#FFFFFF')
        style.map('TButton',
                  background=[('active', '#4D4D4D')],
                  foreground=[('active', '#FFFFFF')])
        style.configure('TCheckbutton',
                        background='#2B2B2B',
                        foreground='#FFFFFF')
        style.map('TCheckbutton',
                  background=[('active', '#4D4D4D')],
                  foreground=[('active', '#FFFFFF')])
        style.configure('TEntry',
                        foreground='#FFFFFF',
                        background='#3A3A3A',
                        fieldbackground='#3A3A3A',
                        insertcolor='#FFFFFF')
        style.configure('TCombobox',
                        foreground='#FFFFFF',
                        fieldbackground='#3A3A3A',
                        background='#2B2B2B')
        self.master.configure(bg='#2B2B2B')

        # Playback/Playlist State
        self.original_playlist = []
        self.playlist = []
        self.current_index = 0
        self.playing = False
        self.looping = True
        self.randomize = False

        # Control events
        self.pause_event = threading.Event()
        self.skip_event = threading.Event()
        self.back_event = threading.Event()
        self.previous_event = threading.Event()
        self.skip_to_event = threading.Event()
        self.skip_to_index = None

        # BPM / Tempo
        self.default_bpm = 120.0
        self.user_bpm = 120.0
        self.ticks_per_beat = 480
        self.bpm_tick_times = []
        self.alpha = 0.2
        self.smoothed_bpm = self.default_bpm
        self.bpm_locked = False
        self.ignore_bpm_var = tk.BooleanVar(value=True)

        # Sync BPM
        self.sync_var = tk.BooleanVar(value=False)
        self.sync_stop_event = threading.Event()
        self.sync_thread = None

        # Logging
        self.log_queue = queue.Queue()
        self.log_messages = []

        # MIDI / OSC
        self.midi_out = None
        self.osc_client = None
        self.loop = asyncio.new_event_loop()
        self.midi_queue = asyncio.Queue()
        self.active_notes = {}
        self.osc_server_task = None
        self.loop_thread = None

        # Alarms
        self.alarms = []  # Each entry: { "datetime": dt, "address": str, "args": list, "triggered": bool }

        # Track each burger menu's visibility
        self.content_visible = False      # MIDI/Log
        self.alarm_frame_visible = False  # Alarm
        self.cc_frame_visible = False     # CC

        # Server connection transport and protocol
        self.server_transport = None
        self.server_protocol = None

        # OSC Addresses Mappings
        self.osc_addresses_in = {
            "pause": "/pause",
            "play": "/play",
            "skip": "/skip",
            "back": "/back",
            "previous": "/previous",
            "bpm": "/bpm",
            "bpm1": "/bpm1",
            "resetbpm": "/resetbpm",
        }

        self.osc_addresses_out = {
            "sync": "/sync",
            "chXnote": "/chXnote",
            "chXnvalue": "/chXnvalue",
            "chXnoteoff": "/chXnoteoff",
            "chXnoffvalue": "/chXnoffvalue",
            "chXcc": "/chXcc",
            "chXccvalue": "/chXccvalue",
            "chXpitch": "/chXpitch",
            "chXpressure": "/chXpressure",
        }

        # Store default OSC addresses for reset functionality
        self.default_osc_addresses_in = self.osc_addresses_in.copy()
        self.default_osc_addresses_out = self.osc_addresses_out.copy()

        # Load icon (optional)
        self.load_icon()

        # Load config
        self.load_config()

        # Build UI
        self.setup_ui()

        # Start clock & alarm checks
        self.update_clock()
        self.check_alarms()

        # Display initial addresses
        self.display_osc_addresses()

        # Start log polling
        self.master.after(100, self.poll_log_queue)

        # Setup protocol handler for window close
        self.master.protocol("WM_DELETE_WINDOW", self.quit_app)

    def load_icon(self):
        try:
            icon_path = os.path.join(os.path.dirname(__file__), "icon.png")
            self.master.iconphoto(False, tk.PhotoImage(file=icon_path))
        except Exception as e:
            print(f"Error loading icon: {e}")

    def load_config(self):
        if os.path.exists(self.CONFIG_FILE):
            with open(self.CONFIG_FILE, 'r') as f:
                config = json.load(f)
                self.saved_port = config.get("osc_in_port", "5550")
                self.saved_midi_port = config.get("midi_input_port", "")
                self.saved_midi_out_port = config.get("midi_output_port", "")
                self.saved_out_ip = config.get("osc_out_ip", self.get_local_ip())
                self.saved_out_port = config.get("osc_out_port", "3330")
                # Load OSC addresses
                self.osc_addresses_in.update(config.get("osc_addresses_in", {}))
                self.osc_addresses_out.update(config.get("osc_addresses_out", {}))
        else:
            self.saved_port = "5550"
            self.saved_midi_port = ""
            self.saved_midi_out_port = ""
            self.saved_out_ip = self.get_local_ip()
            self.saved_out_port = "3330"

    def save_config(self):
        config = {
            "osc_in_port": self.saved_port,
            "midi_input_port": self.saved_midi_port,
            "midi_output_port": self.saved_midi_out_port,
            "osc_out_ip": self.saved_out_ip,
            "osc_out_port": self.saved_out_port,
            "osc_addresses_in": self.osc_addresses_in,
            "osc_addresses_out": self.osc_addresses_out,
        }
        with open(self.CONFIG_FILE, 'w') as f:
            json.dump(config, f, indent=4)

    def setup_ui(self):
        # Increase the base window size a bit
        self.master.geometry("500x350")

        # ------------- Menu Bar ------------- #
        menu_bar = tk.Menu(self.master, bg='#2B2B2B', fg='#FFFFFF')
        self.master.config(menu=menu_bar)

        # Help Menu
        help_menu = tk.Menu(menu_bar, tearoff=0, bg='#2B2B2B', fg='#FFFFFF')
        menu_bar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="OSC Commands", command=self.show_help)

        # Addresses Menu
        addresses_menu = tk.Menu(menu_bar, tearoff=0, bg='#2B2B2B', fg='#FFFFFF')
        menu_bar.add_cascade(label="Addresses", menu=addresses_menu)
        addresses_menu.add_command(label="Edit OSC Addresses", command=self.open_addresses_editor)

        # ------------- Settings Frame (top area) ------------- #
        settings_frame = ttk.Frame(self.master)
        settings_frame.pack(padx=10, pady=10, fill=tk.X)

        ttk.Label(settings_frame, text="IP for OSC In:").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.ip_entry = ttk.Entry(settings_frame)
        self.saved_ip = self.get_local_ip()
        self.ip_entry.insert(0, self.saved_ip)
        self.ip_entry.config(state='readonly')
        self.ip_entry.grid(row=0, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.ip_entry, "Local IP address for OSC server.")

        ttk.Label(settings_frame, text="Port for OSC In:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.port_entry = ttk.Entry(settings_frame)
        self.port_entry.insert(0, self.saved_port)
        self.port_entry.grid(row=1, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.port_entry, "Port number where OSC server listens.")

        ttk.Label(settings_frame, text="Select MIDI Input:").grid(row=2, column=0, sticky=tk.W, pady=2)
        self.midi_input_combo = ttk.Combobox(settings_frame, values=self.get_midi_ports())
        self.midi_input_combo.set(self.saved_midi_port)
        self.midi_input_combo.grid(row=2, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.midi_input_combo, "Choose your MIDI input device (optional).")

        ttk.Label(settings_frame, text="Select MIDI Output:").grid(row=3, column=0, sticky=tk.W, pady=2)
        self.midi_out_combo = ttk.Combobox(settings_frame, values=self.get_midi_output_ports())
        self.midi_out_combo.set(self.saved_midi_out_port)
        self.midi_out_combo.grid(row=3, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.midi_out_combo, "Choose your MIDI output device (optional).")

        ttk.Label(settings_frame, text="IP for OSC Out:").grid(row=4, column=0, sticky=tk.W, pady=2)
        self.output_ip_entry = ttk.Entry(settings_frame)
        self.output_ip_entry.insert(0, self.saved_out_ip)
        self.output_ip_entry.grid(row=4, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.output_ip_entry, "Destination IP address for OSC messages.")

        ttk.Label(settings_frame, text="Port for OSC Out:").grid(row=5, column=0, sticky=tk.W, pady=2)
        self.output_port_entry = ttk.Entry(settings_frame)
        self.output_port_entry.insert(0, self.saved_out_port)
        self.output_port_entry.grid(row=5, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.output_port_entry, "Destination port for OSC messages.")

        # Shared Socket ID (1-4)
        ttk.Label(settings_frame, text="Shared Socket ID:").grid(row=6, column=0, sticky=tk.W, pady=2)
        self.shared_socket_combo = ttk.Combobox(settings_frame, values=["1", "2", "3", "4"], width=5)
        self.shared_socket_combo.current(0)  # Default to "1"
        self.shared_socket_combo.grid(row=6, column=1, sticky=tk.W, pady=2)
        Tooltip(self.shared_socket_combo, "Pick 1-4 if multiple apps share the same port.\nAll must set the same port & enable SO_REUSEPORT if supported.")

        settings_frame.columnconfigure(1, weight=1)

        # Start Server Button Frame
        server_frame = ttk.Frame(self.master)
        server_frame.pack(pady=5)

        self.start_button = ttk.Button(server_frame, text="Start Server", command=self.start)
        self.start_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.start_button, "Start or stop the OSC server (MIDI optional).")

        # Connection Indicator
        self.connection_indicator = tk.Canvas(server_frame, width=20, height=20, bg='#2B2B2B', highlightthickness=0)
        self.connection_indicator.pack(side=tk.LEFT, padx=5)
        self.indicator = self.connection_indicator.create_oval(5, 5, 15, 15, fill='red')

        # ------ Frame for Burger Menus side-by-side ------
        burger_frame = ttk.Frame(self.master)
        burger_frame.pack(pady=2)

        # Burger Menu 1 (MIDI/Log)
        self.menu_button = ttk.Button(burger_frame, text="≡ Midi Player/Log",
                                      command=self.toggle_midi_menu, width=17)
        self.menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.menu_button, "Show/Hide MIDI Player and Log UI.")

        # Burger Menu 2 (Alarm Clock)
        self.alarm_menu_button = ttk.Button(burger_frame, text="≡ Alarm Clock",
                                            command=self.toggle_alarm_menu, width=17)
        self.alarm_menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.alarm_menu_button, "Show/Hide the Alarm Clock scheduling UI.")

        # Burger Menu 3 (CC)
        self.cc_menu_button = ttk.Button(burger_frame, text="≡ CC",
                                         command=self.toggle_cc_menu, width=17)
        self.cc_menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.cc_menu_button, "Show/Hide the CC Controls UI.")

        # Content Frame (MIDI/Log) - hidden initially
        self.content_frame = ttk.Frame(self.master)
        self.setup_midi_ui()

        # Alarm Frame (Scheduling) - hidden initially
        self.alarm_frame = ttk.Frame(self.master)
        self.setup_alarm_ui()

        # CC Frame - hidden initially
        self.cc_frame = ttk.Frame(self.master)
        self.setup_cc_ui()

        self.load_bottom_logo()

    def setup_midi_ui(self):
        # MIDI/Log UI
        controls_frame = ttk.Frame(self.content_frame)
        controls_frame.pack(pady=5)

        self.play_button = ttk.Button(controls_frame, text="Play", command=self.play)
        self.play_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.play_button, "Start playlist playback.")

        self.stop_button = ttk.Button(controls_frame, text="Stop", command=self.stop)
        self.stop_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.stop_button, "Stop playback.")

        self.skip_button = ttk.Button(controls_frame, text="Skip", command=self.skip)
        self.skip_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.skip_button, "Skip to the next file in the playlist.")

        self.back_button = ttk.Button(controls_frame, text="Back", command=self.back)
        self.back_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.back_button, "Restart the current file from the beginning.")

        self.previous_button = ttk.Button(controls_frame, text="Previous", command=self.previous)
        self.previous_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.previous_button, "Load the previous MIDI file in the playlist.")

        file_controls_frame = ttk.Frame(self.content_frame)
        file_controls_frame.pack(pady=5)

        self.load_button = ttk.Button(file_controls_frame, text="Load MIDI", command=self.load_file)
        self.load_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.load_button, "Load a single MIDI file into the playlist.")

        self.load_folder_button = ttk.Button(file_controls_frame, text="Load Folder", command=self.load_folder)
        self.load_folder_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.load_folder_button, "Load all MIDI files from a selected folder into the playlist.")

        self.unload_button = ttk.Button(file_controls_frame, text="Unload Playlist", command=self.unload_playlist)
        self.unload_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.unload_button, "Clear all files from the playlist.")

        playback_options_frame = ttk.Frame(self.content_frame)
        playback_options_frame.pack(pady=5)

        self.looping_var = tk.BooleanVar(value=self.looping)
        self.looping_checkbutton = ttk.Checkbutton(
            playback_options_frame,
            text="Loop Playlist",
            variable=self.looping_var,
            command=self.toggle_looping
        )
        self.looping_checkbutton.pack(side=tk.LEFT, padx=5)
        Tooltip(self.looping_checkbutton, "Enable or disable looping.")

        self.randomize_button = ttk.Button(
            playback_options_frame,
            text="Randomize Playlist",
            command=self.toggle_randomize_playlist
        )
        self.randomize_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.randomize_button, "Shuffle or restore the playlist order.")

        self.sync_checkbutton = ttk.Checkbutton(
            playback_options_frame,
            text="Sync BPM",
            variable=self.sync_var,
            command=self.toggle_sync
        )
        self.sync_checkbutton.pack(side=tk.LEFT, padx=5)
        Tooltip(self.sync_checkbutton, "Enable or disable sending /sync messages.")

        self.info_label = tk.Label(self.content_frame, text="No file loaded",
                                   fg="#FFFFFF", bg="#2B2B2B")
        self.info_label.pack(pady=5)

        bpm_frame = ttk.Frame(self.content_frame)
        bpm_frame.pack(pady=5, fill=tk.X)

        ttk.Label(bpm_frame, text="Tempo (BPM):").pack(side=tk.LEFT)
        self.bpm_slider = tk.Scale(
            bpm_frame,
            from_=20,
            to=420,
            orient=tk.HORIZONTAL,
            command=self.update_bpm,
            bg='#2B2B2B',
            fg='#FFFFFF',
            highlightbackground='#2B2B2B',
            troughcolor='#3A3A3A',
            activebackground='#4D4D4D'
        )
        self.bpm_slider.set(self.user_bpm)
        self.bpm_slider.pack(side=tk.LEFT, padx=5)

        self.reset_bpm_button = ttk.Button(bpm_frame, text="Reset Tempo", command=self.reset_bpm)
        self.reset_bpm_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.reset_bpm_button, "Reset BPM to default.")

        self.lock_bpm_button = ttk.Button(bpm_frame, text="Lock Tempo", command=self.toggle_lock_bpm)
        self.lock_bpm_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.lock_bpm_button, "Lock or unlock BPM slider.")

        self.ignore_bpm_checkbox = ttk.Checkbutton(
            bpm_frame,
            text="Ignore /bpm",
            variable=self.ignore_bpm_var,
            command=self.toggle_ignore_bpm
        )
        self.ignore_bpm_checkbox.pack(side=tk.LEFT, padx=5)
        Tooltip(self.ignore_bpm_checkbox, "Ignore incoming /bpm OSC messages.")

        tk.Label(self.content_frame, text="Log Messages:", bg='#2B2B2B', fg='#FFFFFF').pack()
        log_frame = ttk.Frame(self.content_frame)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10)

        self.log_text = tk.Text(
            log_frame,
            height=8,
            width=70,
            state='disabled',
            bg='#1E1E1E',
            fg='#FFFFFF',
            insertbackground='#FFFFFF',
            wrap='word'
        )
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        log_scroll = ttk.Scrollbar(log_frame, command=self.log_text.yview)
        self.log_text.config(yscrollcommand=log_scroll.set)
        log_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        tk.Label(self.content_frame, text="Playlist:", bg='#2B2B2B', fg='#FFFFFF').pack()
        playlist_frame = ttk.Frame(self.content_frame)
        playlist_frame.pack(fill=tk.BOTH, expand=True, padx=10)

        self.playlist_box = tk.Listbox(
            playlist_frame,
            selectmode=tk.SINGLE,
            bg='#1E1E1E',
            fg='#FFFFFF',
            highlightbackground='#1E1E1E',
            selectbackground='#3A3A3A',
            height=10
        )
        self.playlist_box.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        playlist_scroll = ttk.Scrollbar(playlist_frame, command=self.playlist_box.yview)
        self.playlist_box.config(yscrollcommand=playlist_scroll.set)
        playlist_scroll.pack(side=tk.RIGHT, fill=tk.Y)

    def setup_alarm_ui(self):
        # Alarm Clock UI
        time_frame = ttk.Frame(self.alarm_frame)
        time_frame.pack(pady=5, fill=tk.X)
        self.clock_label = tk.Label(time_frame, text="Current Time: --:--:--", bg="#2B2B2B", fg="#FFFFFF")
        self.clock_label.pack(side=tk.LEFT, padx=5)

        schedule_frame = ttk.Frame(self.alarm_frame)
        schedule_frame.pack(pady=5, fill=tk.X)

        now = datetime.now()
        default_date_str = now.strftime("%Y-%m-%d")
        default_time_str = (now + timedelta(minutes=2)).strftime("%H:%M:%S")

        ttk.Label(schedule_frame, text="Date (YYYY-MM-DD):").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.alarm_date_entry = ttk.Entry(schedule_frame, width=12)
        self.alarm_date_entry.grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        self.alarm_date_entry.insert(0, default_date_str)

        ttk.Label(schedule_frame, text="Time (HH:MM:SS):").grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
        self.alarm_time_entry = ttk.Entry(schedule_frame, width=10)
        self.alarm_time_entry.grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
        self.alarm_time_entry.insert(0, default_time_str)

        ttk.Label(schedule_frame, text="OSC Address:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
        self.alarm_address_entry = ttk.Entry(schedule_frame, width=20)
        self.alarm_address_entry.grid(row=2, column=1, sticky=tk.W, padx=5, pady=5)
        self.alarm_address_entry.insert(0, "/clock")

        ttk.Label(schedule_frame, text="OSC Args:").grid(row=3, column=0, sticky=tk.W, padx=5, pady=5)
        self.alarm_args_entry = ttk.Entry(schedule_frame, width=20)
        self.alarm_args_entry.grid(row=3, column=1, sticky=tk.W, padx=5, pady=5)
        self.alarm_args_entry.insert(0, "1.0")

        self.schedule_alarm_button = ttk.Button(schedule_frame, text="Schedule Alarm", command=self.schedule_alarm)
        self.schedule_alarm_button.grid(row=4, column=0, columnspan=2, pady=5)
        Tooltip(self.schedule_alarm_button, "Schedule a new alarm.")

        tk.Label(self.alarm_frame, text="Scheduled Alarms:", bg='#2B2B2B', fg='#FFFFFF').pack()
        alarm_list_frame = ttk.Frame(self.alarm_frame)
        alarm_list_frame.pack(fill=tk.BOTH, expand=True, padx=10)

        self.alarm_listbox = tk.Listbox(
            alarm_list_frame,
            selectmode=tk.SINGLE,
            bg='#1E1E1E',
            fg='#FFFFFF',
            highlightbackground='#1E1E1E',
            selectbackground='#3A3A3A',
            height=8
        )
        self.alarm_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        alarm_scroll = ttk.Scrollbar(alarm_list_frame, command=self.alarm_listbox.yview)
        self.alarm_listbox.config(yscrollcommand=alarm_scroll.set)
        alarm_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.remove_alarm_button = ttk.Button(self.alarm_frame, text="Remove Selected Alarm", command=self.remove_selected_alarm)
        self.remove_alarm_button.pack(pady=5)
        Tooltip(self.remove_alarm_button, "Remove the selected alarm.")

    def setup_cc_ui(self):
        """
        Creates the widgets for 6 CC sliders (0–127), 6 on/off toggles,
        and 6 custom OSC address input fields.
        """
        self.cc_sliders = []
        self.cc_toggles = []
        self.cc_address_entries = []

        ttk.Label(self.cc_frame, text="CC Controls", foreground='#FFFFFF').pack(pady=5)

        cc_controls_frame = ttk.Frame(self.cc_frame)
        cc_controls_frame.pack(padx=10, pady=10, fill=tk.X)

        for i in range(6):
            row_frame = ttk.Frame(cc_controls_frame)
            row_frame.pack(fill=tk.X, pady=3)

            # Label
            ttk.Label(row_frame, text=f"CC #{i+1}:", width=10).pack(side=tk.LEFT, padx=5)

            # Slider
            slider = tk.Scale(row_frame, from_=0, to=127, orient=tk.HORIZONTAL,
                              length=150, bg='#2B2B2B', fg='#FFFFFF',
                              highlightbackground='#2B2B2B',
                              troughcolor='#3A3A3A',
                              activebackground='#4D4D4D')
            slider.set(0)
            slider.pack(side=tk.LEFT, padx=5)
            self.cc_sliders.append(slider)

            # Bind the slider to send OSC on change
            slider.bind("<ButtonRelease-1>", lambda event, idx=i: self.send_cc_message(idx))

            # Toggle
            toggle_var = tk.BooleanVar(value=False)
            toggle_btn = ttk.Checkbutton(row_frame, text="On/Off", variable=toggle_var,
                                         command=lambda idx=i: self.send_cc_toggle(idx))
            toggle_btn.pack(side=tk.LEFT, padx=5)
            self.cc_toggles.append(toggle_var)

            # OSC Address
            addr_entry = ttk.Entry(row_frame, width=15)
            addr_entry.insert(0, f"/myCC{i+1}")  # default address
            addr_entry.pack(side=tk.LEFT, padx=5)
            self.cc_address_entries.append(addr_entry)

    def show_help(self):
        help_window = tk.Toplevel(self.master)
        help_window.title("Help - OSC Commands")
        help_window.geometry("500x600")
        help_window.resizable(False, False)

        # Make it modal
        help_window.transient(self.master)
        help_window.grab_set()

        text = tk.Text(help_window, wrap='word', bg='#2B2B2B', fg='#FFFFFF', font=("Courier", 10))
        text.pack(expand=True, fill='both', padx=10, pady=10)

        osc_commands = """
------ Incoming OSC Addresses ------
/pause
    Pause playback.

 /play
    Resume playback.

 /skip
    Skip to next track.

 /back
    Restart current track.

 /previous
    Return to previous track.

 /bpm
    Set BPM via OSC.

 /bpm1
    Toggle ignoring BPM sync.

 /resetbpm
    Reset BPM to song's default.

 /1 - /50
    Load specific song by number by /X (X=1-50).

------ Outgoing OSC Addresses ------
/sync
    Sent periodically with BPM value.

 /chXnote
    Note on.

 /chXnvalue
    Note velocity, range 0-127.

 /chXnoteoff
    Note off.

 /chXnoffvalue
    Note off velocity, range 0-127.

 /chXcc
    Control Change number, range 0-127.

 /chXccvalue
    Control Change value scaled, range 0-1.

 /chXpitch
    Pitch wheel.

 /chXpressure
    Aftertouch.
"""
        text.insert('1.0', osc_commands)
        text.config(state='disabled')

    def open_addresses_editor(self):
        editor_window = tk.Toplevel(self.master)
        editor_window.title("Edit OSC Addresses")
        editor_window.geometry("600x700")
        editor_window.resizable(False, False)

        # Make it modal
        editor_window.transient(self.master)
        editor_window.grab_set()

        notebook = ttk.Notebook(editor_window)
        notebook.pack(expand=True, fill='both', padx=10, pady=10)

        incoming_frame = ttk.Frame(notebook)
        notebook.add(incoming_frame, text="Incoming Addresses")

        outgoing_frame = ttk.Frame(notebook)
        notebook.add(outgoing_frame, text="Outgoing Addresses")

        incoming_entries = {}
        outgoing_entries = {}

        def create_address_fields(frame, addresses, entries):
            for idx, (action, address) in enumerate(addresses.items()):
                ttk.Label(frame, text=f"{action.capitalize()} Address:").grid(row=idx, column=0, sticky=tk.W, padx=5, pady=5)
                entry = ttk.Entry(frame, width=30)
                entry.grid(row=idx, column=1, sticky=tk.W, padx=5, pady=5)
                entry.insert(0, address)
                entries[action] = entry

        create_address_fields(incoming_frame, self.osc_addresses_in, incoming_entries)
        create_address_fields(outgoing_frame, self.osc_addresses_out, outgoing_entries)

        buttons_frame = ttk.Frame(editor_window)
        buttons_frame.pack(pady=10)

        save_button = ttk.Button(buttons_frame, text="Save Addresses",
                                 command=lambda: self.save_addresses(editor_window, incoming_entries, outgoing_entries))
        save_button.pack(side=tk.LEFT, padx=5)
        Tooltip(save_button, "Save the updated OSC addresses.")

        reset_button = ttk.Button(buttons_frame, text="Reset to Default",
                                  command=lambda: self.reset_addresses(incoming_entries, outgoing_entries))
        reset_button.pack(side=tk.LEFT, padx=5)
        Tooltip(reset_button, "Reset OSC addresses to default values.")

    def reset_addresses(self, incoming_entries, outgoing_entries):
        for action, entry in incoming_entries.items():
            default_address = self.default_osc_addresses_in.get(action, "")
            entry.delete(0, tk.END)
            entry.insert(0, default_address)
            self.osc_addresses_in[action] = default_address

        for action, entry in outgoing_entries.items():
            default_address = self.default_osc_addresses_out.get(action, "")
            entry.delete(0, tk.END)
            entry.insert(0, default_address)
            self.osc_addresses_out[action] = default_address

        self.save_config()
        self.log_message("OSC Addresses reset to default and saved.")
        messagebox.showinfo("Reset Successful", "OSC Addresses have been reset to default values.")

    def save_addresses(self, window, incoming_entries, outgoing_entries):
        for action, widget in incoming_entries.items():
            new_address = widget.get().strip()
            if not new_address.startswith("/"):
                messagebox.showerror("Invalid Address", f"Incoming address for '{action}' must start with '/'.")
                return
            self.osc_addresses_in[action] = new_address

        for action, widget in outgoing_entries.items():
            new_address = widget.get().strip()
            if not new_address.startswith("/"):
                messagebox.showerror("Invalid Address", f"Outgoing address for '{action}' must start with '/'.")
                return
            self.osc_addresses_out[action] = new_address

        self.save_config()
        self.log_message("OSC Addresses updated and saved.")
        messagebox.showinfo("Success", "OSC Addresses have been updated successfully.")

        if self.server_transport:
            self.log_message("Reloading OSC dispatcher with new addresses.")
            self.reload_dispatcher()
        window.destroy()

    def reload_dispatcher(self):
        if not self.server_protocol:
            return
        disp = dispatcher.Dispatcher()
        disp.map(self.osc_addresses_in["pause"], self.handle_pause)
        disp.map(self.osc_addresses_in["play"], self.handle_play)
        disp.map(self.osc_addresses_in["skip"], self.handle_skip)
        disp.map(self.osc_addresses_in["back"], self.handle_back)
        disp.map(self.osc_addresses_in["previous"], self.handle_previous)
        disp.map(self.osc_addresses_in["bpm"], self.handle_bpm)
        disp.map(self.osc_addresses_in["bpm1"], self.handle_bpm1_toggle)
        disp.map(self.osc_addresses_in["resetbpm"], self.handle_resetbpm)
        for i in range(1, 51):
            disp.map(f"/{i}", self.handle_numeric_skip)

        self.server_protocol.dispatcher = disp
        self.log_message("OSC Dispatcher reloaded with updated addresses.")

    def schedule_alarm(self):
        date_str = self.alarm_date_entry.get().strip()
        time_str = self.alarm_time_entry.get().strip()
        address = self.alarm_address_entry.get().strip()
        args_str = self.alarm_args_entry.get().strip()

        if not date_str or not time_str or not address:
            messagebox.showwarning("Incomplete Data", "Please enter Date, Time (HH:MM:SS), and OSC Address.")
            return

        try:
            alarm_datetime = datetime.strptime(f"{date_str} {time_str}", "%Y-%m-%d %H:%M:%S")
            if alarm_datetime <= datetime.now():
                messagebox.showwarning("Invalid Time", "Alarm time must be in the future.")
                return
        except ValueError:
            messagebox.showwarning("Invalid Date/Time", "Use YYYY-MM-DD and HH:MM:SS (24-hour).")
            return

        args = args_str.split() if args_str else []

        alarm_entry = {
            "datetime": alarm_datetime,
            "address": address,
            "args": args,
            "triggered": False
        }
        self.alarms.append(alarm_entry)
        display_text = f"{alarm_datetime.strftime('%Y-%m-%d %H:%M:%S')} -> {address} {' '.join(args)}"
        self.alarm_listbox.insert(tk.END, display_text)

        self.log_message(f"Scheduled alarm at {alarm_datetime}, address={address}, args={args}")

        now = datetime.now()
        default_date_str = now.strftime("%Y-%m-%d")
        default_time_str = (now + timedelta(minutes=2)).strftime("%H:%M:%S")
        self.alarm_date_entry.delete(0, tk.END)
        self.alarm_time_entry.delete(0, tk.END)
        self.alarm_date_entry.insert(0, default_date_str)
        self.alarm_time_entry.insert(0, default_time_str)
        self.alarm_address_entry.delete(0, tk.END)
        self.alarm_address_entry.insert(0, "/clock")
        self.alarm_args_entry.delete(0, tk.END)
        self.alarm_args_entry.insert(0, "1.0")

    def remove_selected_alarm(self):
        selection = self.alarm_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select an alarm to remove.")
            return
        index = selection[0]
        self.alarm_listbox.delete(index)
        del self.alarms[index]
        self.log_message(f"Removed alarm at index {index}.")

    def update_clock(self):
        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.clock_label.config(text=f"Current Time: {now_str}")
        self.master.after(1000, self.update_clock)

    def check_alarms(self):
        now = datetime.now()
        for alarm in self.alarms:
            if not alarm["triggered"] and now >= alarm["datetime"]:
                address = alarm["address"]
                args = alarm["args"]
                self.log_message(f"Alarm triggered -> sending OSC to {address} with args {args}")
                if self.osc_client:
                    if args:
                        parsed_args = []
                        for arg in args:
                            try:
                                val = int(arg)
                                parsed_args.append(val)
                            except ValueError:
                                try:
                                    val = float(arg)
                                    parsed_args.append(val)
                                except ValueError:
                                    parsed_args.append(arg)
                        self.osc_client.send_message(address, parsed_args)
                    else:
                        self.osc_client.send_message(address, [])
                alarm["triggered"] = True
        self.master.after(1000, self.check_alarms)

    def display_osc_addresses(self):
        self.log_message("------ OSC Addresses ------")
        self.log_message("Incoming OSC Addresses:")
        for action, addr in self.osc_addresses_in.items():
            self.log_message(f"  {action.capitalize()}: {addr}")
        self.log_message("Outgoing OSC Addresses:")
        for action, addr in self.osc_addresses_out.items():
            self.log_message(f"  {action.capitalize()}: {addr}")
        self.log_message("------------------------------")

    def toggle_sync(self):
        if self.sync_var.get():
            if not self.sync_thread or not self.sync_thread.is_alive():
                self.sync_stop_event.clear()
                self.sync_thread = threading.Thread(target=self._sync_loop, daemon=True)
                self.sync_thread.start()
                self.log_message("Sync BPM started.")
        else:
            if self.sync_thread and self.sync_thread.is_alive():
                self.sync_stop_event.set()
                self.log_message("Sync BPM stopped.")

    def _sync_loop(self):
        while not self.sync_stop_event.is_set() and self.sync_var.get():
            current_bpm = max(1, round(self.user_bpm))
            interval = 60.0 / current_bpm
            time.sleep(interval)
            if self.sync_stop_event.is_set() or not self.sync_var.get():
                break
            if self.osc_client:
                self.osc_client.send_message(self.osc_addresses_out["sync"], current_bpm)
                self.log_message(f"Sent {self.osc_addresses_out['sync']} at BPM {current_bpm}")

    def log_message(self, message: str):
        if len(self.log_messages) >= self.MAX_LOG_MESSAGES:
            self.log_messages.pop(0)
        self.log_messages.append(message)
        self.log_queue.put(message)

    def poll_log_queue(self):
        while not self.log_queue.empty():
            message = self.log_queue.get()
            self.log_text.config(state="normal")
            self.log_text.insert(tk.END, f"{message}\n")
            if len(self.log_messages) > self.MAX_LOG_MESSAGES:
                self.log_text.delete("1.0", "2.0")
            self.log_text.see(tk.END)
            self.log_text.config(state="disabled")
        self.master.after(100, self.poll_log_queue)

    def clear_log(self):
        self.log_messages.clear()
        self.log_text.config(state='normal')
        self.log_text.delete("1.0", tk.END)
        self.log_text.config(state='disabled')

    def unload_playlist(self):
        if self.playing:
            messagebox.showwarning("Stop Playback", "Please stop playback before unloading the playlist.")
            return
        self.playlist.clear()
        self.original_playlist.clear()
        self.playlist_box.delete(0, tk.END)
        self.info_label.config(text="Playlist unloaded.")
        self.log_message("Playlist unloaded.")

    def update_bpm(self, new_bpm_str):
        if self.bpm_locked:
            return
        try:
            new_bpm = float(new_bpm_str)
            self.smoothed_bpm = self.alpha * new_bpm + (1 - self.alpha) * self.smoothed_bpm
            final_bpm = max(1, round(self.smoothed_bpm))
            self.user_bpm = final_bpm
            self.bpm_slider.set(final_bpm)
            self.log_message(f"User BPM set to {final_bpm}")
        except ValueError:
            pass

    def load_bottom_logo(self):
        try:
            bottom_logo_path = os.path.join(os.path.dirname(__file__), "bottomlogo.ico")
            self.bottom_logo = tk.PhotoImage(file=bottom_logo_path)
            bottom_logo_label = tk.Label(self.master, image=self.bottom_logo, bg='#2B2B2B')
            bottom_logo_label.pack(side=tk.BOTTOM, pady=10)
        except Exception as e:
            print(f"Error loading bottom logo: {e}")

    def reset_bpm(self):
        self.user_bpm = max(1, round(self.default_bpm))
        self.smoothed_bpm = float(self.user_bpm)
        self.bpm_slider.set(self.user_bpm)
        self.log_message(f"Tempo reset to default: {self.user_bpm} BPM")

    def toggle_lock_bpm(self):
        self.bpm_locked = not self.bpm_locked
        if self.bpm_locked:
            self.bpm_slider.config(state='disabled')
            self.lock_bpm_button.config(text="Unlock Tempo")
            self.log_message("BPM slider locked.")
        else:
            self.bpm_slider.config(state='normal')
            self.lock_bpm_button.config(text="Lock Tempo")
            self.log_message("BPM slider unlocked.")

    def toggle_ignore_bpm(self):
        if self.ignore_bpm_var.get():
            self.log_message("Incoming /bpm OSC messages are now ignored.")
        else:
            self.log_message("Incoming /bpm OSC messages are now processed.")

    def load_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("MIDI Files", "*.mid *.midi")])
        if file_path:
            self.playlist.append(file_path)
            self.original_playlist.append(file_path)
            index_num = len(self.playlist)
            display_text = f"{index_num}: {os.path.basename(file_path)}"
            self.playlist_box.insert(tk.END, display_text)
            self.info_label.config(text=f"Loaded: {file_path}")
            self.log_message(f"Loaded MIDI file: {file_path}")
        else:
            self.info_label.config(text="No file selected.")
            self.log_message("No file selected.")

    def load_folder(self):
        folder_path = filedialog.askdirectory()
        if folder_path:
            midi_files = [os.path.join(folder_path, f)
                          for f in os.listdir(folder_path)
                          if f.lower().endswith(('.mid', '.midi'))]
            if midi_files:
                for file in midi_files:
                    self.playlist.append(file)
                    self.original_playlist.append(file)
                    index_num = len(self.playlist)
                    display_text = f"{index_num}: {os.path.basename(file)}"
                    self.playlist_box.insert(tk.END, display_text)
                self.info_label.config(text=f"Loaded {len(midi_files)} MIDI files.")
                self.log_message(f"Loaded {len(midi_files)} files from {folder_path}")
            else:
                messagebox.showinfo("No MIDI Files", "No MIDI files found.")
                self.log_message("No MIDI files found in the selected folder.")
        else:
            self.info_label.config(text="No folder selected.")
            self.log_message("No folder selected.")

    def play(self):
        if not self.playlist:
            self.info_label.config(text="No MIDI files loaded.")
            self.log_message("No MIDI files to play.")
            return

        if not self.playing:
            self.playing = True
            self.current_index = 0
            self.log_message("Playback started.")
            t = threading.Thread(target=self._play_midi_playlist, daemon=True)
            t.start()
        else:
            self.log_message("Playback already running.")

    def stop(self):
        if self.playing:
            self.playing = False
            self.pause_event.clear()
            self.skip_event.set()
            self.back_event.set()
            self.previous_event.set()
            self.skip_to_event.set()
            self.info_label.config(text="Stopped playback.")
            self.log_message("Playback stopped.")

            if self.sync_thread and self.sync_thread.is_alive():
                self.sync_stop_event.set()
                self.log_message("Sync BPM stopped.")

            if self.server_transport:
                self.server_transport.close()
                self.server_transport = None
                self.server_protocol = None
                self.set_connection_status('red')
                self.log_message("OSC Server stopped.")
        else:
            self.log_message("Stop command but nothing playing.")

    def skip(self):
        if self.playing:
            self.skip_event.set()
            self.log_message("Skip requested.")
        else:
            self.log_message("Skip requested but nothing playing.")

    def back(self):
        if self.playing:
            self.back_event.set()
            self.log_message("Restart current track requested.")
        else:
            self.log_message("Back requested but nothing playing.")

    def previous(self):
        if self.playing:
            if self.current_index > 0:
                self.previous_event.set()
                self.log_message("Previous track requested.")
            else:
                self.log_message("Already at first track.")
        else:
            self.log_message("Previous requested but nothing playing.")

    def skip_to_number(self, num):
        if not self.playing:
            self.log_message(f"Skip to {num}, but no playback active.")
            return
        if 1 <= num <= len(self.playlist):
            self.skip_to_index = num - 1
            self.skip_to_event.set()
            self.log_message(f"Skip to file #{num}")
        else:
            self.log_message(f"Invalid file number {num} (out of range).")

    def toggle_looping(self):
        self.looping = self.looping_var.get()
        self.log_message(f"Looping {'enabled' if self.looping else 'disabled'}.")

    def toggle_randomize_playlist(self):
        self.randomize = not self.randomize
        if self.randomize:
            if len(self.playlist) > 1:
                random.shuffle(self.playlist)
                self.update_playlist_box()
                self.current_index = 0
                self.log_message("Playlist randomized.")
            else:
                self.log_message("Not enough MIDI files to randomize.")
        else:
            self.playlist = self.original_playlist.copy()
            self.update_playlist_box()
            self.current_index = 0
            self.log_message("Playlist order restored.")

        self.randomize_button.config(text="Restore Order" if self.randomize else "Randomize Playlist")

    def update_playlist_box(self):
        self.playlist_box.delete(0, tk.END)
        for idx, fpath in enumerate(self.playlist, start=1):
            display_text = f"{idx}: {os.path.basename(fpath)}"
            self.playlist_box.insert(tk.END, display_text)

    def _play_midi_playlist(self):
        try:
            while self.playing and (0 <= self.current_index < len(self.playlist)):
                midi_file_path = self.playlist[self.current_index]
                self._play_single_midi(midi_file_path)
                if not self.playing:
                    break

                if self.previous_event.is_set():
                    self.previous_event.clear()
                    self.current_index = max(0, self.current_index - 1)
                    continue
                if self.back_event.is_set():
                    self.back_event.clear()
                    continue
                if self.skip_to_event.is_set():
                    self.skip_to_event.clear()
                    if self.skip_to_index is not None:
                        if 0 <= self.skip_to_index < len(self.playlist):
                            self.current_index = self.skip_to_index
                        self.skip_to_index = None
                    continue

                if self.looping and self.current_index == len(self.playlist) - 1:
                    if self.randomize and len(self.playlist) > 1:
                        random.shuffle(self.playlist)
                        self.update_playlist_box()
                        self.log_message("Playlist reshuffled for looping.")
                    self.current_index = 0
                else:
                    self.current_index += 1

            if self.playing:
                self.playing = False
                self.info_label.config(text="Playback finished.")
                self.log_message("Playback finished.")
                if self.server_transport:
                    self.server_transport.close()
                    self.server_transport = None
                    self.server_protocol = None
                    self.set_connection_status('red')
                    self.log_message("OSC Server stopped.")
        except Exception as e:
            self.playing = False
            self.log_message(f"Error: {e}")
            self.info_label.config(text=f"Error: {e}")

    def _play_single_midi(self, midi_file_path):
        self.info_label.config(text=f"Playing: {midi_file_path}")
        self.log_message(f"Playing {midi_file_path}")

        try:
            midi_file = MidiFile(midi_file_path)
        except Exception as e:
            self.log_message(f"Failed to load MIDI file: {e}")
            return

        if not self.bpm_locked:
            bpm = self.get_file_bpm(midi_file)
            if bpm:
                self.default_bpm = max(1, round(bpm))
                self.smoothed_bpm = float(self.default_bpm)
                self.user_bpm = self.default_bpm
                self.master.after(0, lambda: self.bpm_slider.set(self.user_bpm))
                self.log_message(f"Default BPM set to {self.default_bpm}")
            else:
                self.log_message("No BPM found in MIDI file; using existing BPM.")

        self.ticks_per_beat = midi_file.ticks_per_beat
        events = []
        for track in midi_file.tracks:
            abs_ticks = 0
            for msg in track:
                abs_ticks += msg.time
                if not msg.is_meta:
                    events.append((abs_ticks, msg))

        events.sort(key=lambda e: e[0])
        last_abs_ticks = 0

        for abs_ticks, msg in events:
            if not self.playing:
                break
            if self.skip_event.is_set():
                self.skip_event.clear()
                break
            if self.previous_event.is_set() or self.back_event.is_set() or self.skip_to_event.is_set():
                break

            while self.pause_event.is_set() and self.playing:
                time.sleep(0.1)

            delta_ticks = abs_ticks - last_abs_ticks
            last_abs_ticks = abs_ticks

            if delta_ticks > 0:
                time_default = (delta_ticks / float(self.ticks_per_beat)) * (60.0 / self.default_bpm)
                ratio = self.default_bpm / float(self.user_bpm)
                if self.user_bpm < 1:
                    self.user_bpm = 1
                time_user = time_default * ratio
                time.sleep(time_user)

            self.handle_midi_message(msg, source='playback')

    def handle_midi_message(self, message, source='input'):
        if hasattr(message, 'channel'):
            ch = message.channel + 1
            if message.type in ('note_on', 'note_off'):
                note = message.note
                velocity = message.velocity
                if source == 'playback':
                    if message.type == 'note_on' and velocity > 0:
                        if self.osc_client:
                            osc_addr = self.osc_addresses_out["chXnote"].replace("X", str(ch))
                            self.osc_client.send_message(osc_addr, note)
                            self.log_message(f"Playback -> {osc_addr} {note}")
                else:
                    if self.osc_client:
                        if message.type == 'note_on' and velocity > 0:
                            osc_addr_note = self.osc_addresses_out["chXnote"].replace("X", str(ch))
                            osc_addr_nvalue = self.osc_addresses_out["chXnvalue"].replace("X", str(ch))
                            self.osc_client.send_message(osc_addr_note, note)
                            self.osc_client.send_message(osc_addr_nvalue, velocity)
                            self.log_message(f"Input -> {osc_addr_note} {note}")
                            self.log_message(f"Input -> {osc_addr_nvalue} {velocity}")
                        else:
                            osc_addr_noteoff = self.osc_addresses_out["chXnoteoff"].replace("X", str(ch))
                            osc_addr_noffvalue = self.osc_addresses_out["chXnoffvalue"].replace("X", str(ch))
                            self.osc_client.send_message(osc_addr_noteoff, note)
                            self.osc_client.send_message(osc_addr_noffvalue, 0)
                            self.log_message(f"Input -> {osc_addr_noteoff} {note}")
                            self.log_message(f"Input -> {osc_addr_noffvalue} 0")
            elif message.type == 'control_change':
                cc_number = message.control
                cc_value = message.value
                if self.osc_client:
                    osc_addr_cc = self.osc_addresses_out["chXcc"].replace("X", str(ch))
                    self.osc_client.send_message(osc_addr_cc, cc_number)
                    self.log_message(f"Input -> {osc_addr_cc} {cc_number}")

                    scaled_value = cc_value / 127.0
                    osc_addr_ccvalue = self.osc_addresses_out["chXccvalue"].replace("X", str(ch))
                    self.osc_client.send_message(osc_addr_ccvalue, float(scaled_value))
                    self.log_message(f"Input -> {osc_addr_ccvalue} {scaled_value:.3f}")
            elif message.type == 'pitchwheel':
                if self.osc_client:
                    osc_address = self.osc_addresses_out["chXpitch"].replace("X", str(ch))
                    self.osc_client.send_message(osc_address, message.pitch)
                    self.log_message(f"Input -> {osc_address} {message.pitch}")
            elif message.type == 'aftertouch':
                if self.osc_client:
                    osc_address = self.osc_addresses_out["chXpressure"].replace("X", str(ch))
                    self.osc_client.send_message(osc_address, message.value)
                    self.log_message(f"Input -> {osc_address} {message.value}")
            else:
                self.log_message(f"Ignored message type: {message.type}")
        else:
            self.log_message(f"Ignored message without channel: {message}")

    def get_file_bpm(self, midi_file):
        for track in midi_file.tracks:
            for msg in track:
                if msg.type == 'set_tempo':
                    return mido.tempo2bpm(msg.tempo)
        return None

    def get_local_ip(self):
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            s.connect(("8.8.8.8", 80))
            ip = s.getsockname()[0]
        except Exception:
            ip = "127.0.0.1"
        finally:
            s.close()
        return ip

    def get_midi_ports(self):
        return mido.get_input_names()

    def get_midi_output_ports(self):
        return mido.get_output_names()

    def start(self):
        if self.start_button['text'] == "Start Server":
            midi_input_port_name = self.midi_input_combo.get()
            midi_output_port_name = self.midi_out_combo.get()
            osc_out_ip = self.output_ip_entry.get()

            try:
                osc_out_port = int(self.output_port_entry.get())
                osc_in_port = int(self.port_entry.get())
            except ValueError:
                messagebox.showerror("Error", "Invalid port number.")
                return

            # Optional MIDI
            if not midi_input_port_name:
                messagebox.showwarning("No MIDI In", "No MIDI input selected. MIDI features may be limited.")
            else:
                try:
                    midi_in = mido.open_input(midi_input_port_name)
                    self.midi_in_thread = threading.Thread(target=self.run_midi_loop, args=(midi_in,), daemon=True)
                    self.midi_in_thread.start()
                except Exception as e:
                    messagebox.showwarning("MIDI Input Error", f"Could not open MIDI input: {e}")

            if not midi_output_port_name:
                messagebox.showwarning("No MIDI Out", "No MIDI output selected. Some playback features may be limited.")
            else:
                try:
                    self.midi_out = mido.open_output(midi_output_port_name)
                except Exception as e:
                    messagebox.showwarning("MIDI Output Error", f"Could not open MIDI output: {e}")

            # Create the OSC client (outgoing)
            self.osc_client = udp_client.SimpleUDPClient(osc_out_ip, osc_out_port)

            # Start the asynchronous OSC server with the chosen port
            self.osc_server_task = asyncio.run_coroutine_threadsafe(
                self.start_osc_server_async(osc_in_port),
                self.loop
            )
            if not self.loop.is_running():
                self.loop_thread = threading.Thread(target=self.loop.run_forever, daemon=True)
                self.loop_thread.start()

            # Save config
            self.saved_out_ip = osc_out_ip
            self.saved_out_port = osc_out_port
            self.saved_port = osc_in_port
            self.saved_midi_port = midi_input_port_name
            self.saved_midi_out_port = midi_output_port_name
            self.save_config()

            self.start_button.config(text="Stop and Quit")
            self.log_message("OSC Server started (MIDI optional).")
        else:
            self.stop()

    async def start_osc_server_async(self, port):
        disp = dispatcher.Dispatcher()
        disp.map(self.osc_addresses_in["pause"], self.handle_pause)
        disp.map(self.osc_addresses_in["play"], self.handle_play)
        disp.map(self.osc_addresses_in["skip"], self.handle_skip)
        disp.map(self.osc_addresses_in["back"], self.handle_back)
        disp.map(self.osc_addresses_in["previous"], self.handle_previous)
        disp.map(self.osc_addresses_in["bpm"], self.handle_bpm)
        disp.map(self.osc_addresses_in["bpm1"], self.handle_bpm1_toggle)
        disp.map(self.osc_addresses_in["resetbpm"], self.handle_resetbpm)
        for i in range(1, 51):
            disp.map(f"/{i}", self.handle_numeric_skip)

        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
            self.log_message("SO_REUSEPORT enabled (if supported).")
        except AttributeError:
            self.log_message("SO_REUSEPORT not available on this platform.")

        try:
            sock.bind(("0.0.0.0", port))
            self.log_message(f"OSC Server bound to port {port}.")
            self.set_connection_status('green')
        except OSError as e:
            self.log_message(f"Error binding to port {port}: {e}")
            messagebox.showerror("Binding Error", f"Could not bind to port {port}: {e}")
            self.set_connection_status('red')
            return

        self.log_message(f"Async OSC Server binding on port {port}...")
        server = osc_server.AsyncIOOSCUDPServer(
            None,
            disp,
            self.loop,
            sock=sock
        )
        transport, protocol = await server.create_serve_endpoint()
        self.server_transport = transport
        self.server_protocol = protocol
        self.log_message(f"Async OSC Server started on port {port} with shared socket.")

    def set_connection_status(self, color):
        if color not in ['red', 'green']:
            color = 'red'
        self.master.after(0, lambda: self.connection_indicator.itemconfig(self.indicator, fill=color))

    def handle_previous(self, address, *args):
        self.previous()

    def handle_numeric_skip(self, address, *args):
        match_obj = re.match(r'^/(\d+)$', address)
        if match_obj:
            num = int(match_obj.group(1))
            self.skip_to_number(num)
        else:
            self.log_message(f"Unhandled numeric OSC address: {address}")

    def handle_bpm1_toggle(self, address, *args):
        current = self.ignore_bpm_var.get()
        new_val = not current
        self.ignore_bpm_var.set(new_val)
        self.log_message(f"'{self.osc_addresses_in['bpm1']}' toggled -> ignoring /bpm = {new_val}")

    def handle_resetbpm(self, address, *args):
        if not self.playing:
            self.log_message("Received /resetbpm but playback not running.")
            return
        self.user_bpm = max(1, round(self.default_bpm))
        self.smoothed_bpm = float(self.user_bpm)
        self.bpm_slider.set(self.user_bpm)
        self.log_message("BPM reset via /resetbpm to current MIDI's default.")

    def handle_pause(self, address, *args):
        if self.playing and not self.pause_event.is_set():
            self.pause_event.set()
            self.info_label.config(text="Playback paused.")
            self.log_message("Playback paused (OSC).")

    def handle_play(self, address, *args):
        if self.playing and self.pause_event.is_set():
            self.pause_event.clear()
            self.info_label.config(text="Playback resumed.")
            self.log_message("Playback resumed (OSC).")

    def handle_skip(self, address, *args):
        if self.playing:
            self.skip_event.set()
            self.log_message("Skip requested (OSC).")
        else:
            self.log_message("Skip but no playback active.")

    def handle_back(self, address, *args):
        if self.playing:
            self.back_event.set()
            self.log_message("Back requested (OSC).")
        else:
            self.log_message("Back but no playback active.")

    def handle_bpm(self, address, *args):
        if self.bpm_locked or self.ignore_bpm_var.get():
            self.log_message(f"Got {address}, but locked or ignored.")
            return
        now = time.time()
        self.bpm_tick_times.append(now)
        if len(self.bpm_tick_times) > 4:
            self.bpm_tick_times.pop(0)
        if len(self.bpm_tick_times) == 4:
            intervals = []
            for i in range(3):
                intervals.append(self.bpm_tick_times[i+1] - self.bpm_tick_times[i])
            avg_interval = sum(intervals) / len(intervals)
            new_bpm = 60.0 / avg_interval
            self.smoothed_bpm = self.alpha * new_bpm + (1 - self.alpha) * self.smoothed_bpm
            final_bpm = max(1, round(self.smoothed_bpm))
            self.user_bpm = final_bpm
            self.master.after(0, lambda: self.bpm_slider.set(final_bpm))
            self.log_message(f"{address} -> {final_bpm}")

    def run_midi_loop(self, midi_in):
        asyncio.set_event_loop(self.loop)
        self.loop.create_task(self.midi_to_osc(midi_in))

    async def midi_to_osc(self, midi_in):
        while True:
            for message in midi_in.iter_pending():
                self.handle_midi_message(message, source='input')
            await asyncio.sleep(0.01)

    def quit_app(self):
        try:
            if self.midi_out:
                self.midi_out.close()
        except Exception as e:
            print(f"Error closing MIDI out: {e}")
        finally:
            self.playing = False
            self.pause_event.clear()
            self.skip_event.set()
            self.back_event.set()
            self.previous_event.set()
            self.skip_to_event.set()
            self.sync_stop_event.set()
            if self.sync_thread and self.sync_thread.is_alive():
                self.sync_thread.join(timeout=1)
            if self.server_transport:
                self.server_transport.close()
                self.server_transport = None
                self.server_protocol = None
                self.set_connection_status('red')
                self.log_message("OSC Server stopped.")
            self.loop.call_soon_threadsafe(self.loop.stop)
            if hasattr(self, 'loop_thread') and self.loop_thread and self.loop_thread.is_alive():
                self.loop_thread.join(timeout=1)
            self.master.quit()

    # ----------------------- Toggling the 3 frames & auto-resize ------------------------------ #
    def toggle_midi_menu(self):
        # Hide other frames first
        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")

        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")

        # Toggle this one
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")
            self.log_message("MIDI Player/Log UI hidden.")
        else:
            self.content_frame.pack(fill=tk.BOTH, expand=True)
            self.content_visible = True
            self.menu_button.config(text="≡ Hide Midi Player/Log")
            self.log_message("MIDI Player/Log UI shown.")

        self.master.update_idletasks()
        self.master.geometry("")

    def toggle_alarm_menu(self):
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")

        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")

        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")
            self.log_message("Alarm Clock UI hidden.")
        else:
            self.alarm_frame.pack(fill=tk.BOTH, expand=True)
            self.alarm_frame_visible = True
            self.alarm_menu_button.config(text="≡ Hide Alarm Clock")
            self.log_message("Alarm Clock UI shown.")

        self.master.update_idletasks()
        self.master.geometry("")

    def toggle_cc_menu(self):
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")

        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")

        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")
            self.log_message("CC UI hidden.")
        else:
            self.cc_frame.pack(fill=tk.BOTH, expand=True)
            self.cc_frame_visible = True
            self.cc_menu_button.config(text="≡ Hide CC")
            self.log_message("CC UI shown.")

        self.master.update_idletasks()
        self.master.geometry("")

    # -------------------- CC Controls -------------------- #
    def send_cc_message(self, idx):
        """
        Sends an OSC message based on the slider value and its corresponding OSC address.
        """
        osc_address = self.cc_address_entries[idx].get().strip()
        value = self.cc_sliders[idx].get()

        if not osc_address.startswith("/"):
            self.log_message(f"Invalid OSC address for CC #{idx+1}: {osc_address}")
            messagebox.showerror("Invalid OSC Address", f"OSC address for CC #{idx+1} must start with '/'.")
            return

        if self.osc_client:
            try:
                self.osc_client.send_message(osc_address, value)
                self.log_message(f"Sent OSC to {osc_address} with value {value}")
            except Exception as e:
                self.log_message(f"Failed to send OSC message to {osc_address}: {e}")
        else:
            self.log_message("OSC Client not connected. Cannot send CC message.")

    def send_cc_toggle(self, idx):
        """
        Sends an OSC message based on the toggle state and its corresponding OSC address.
        """
        osc_address = self.cc_address_entries[idx].get().strip()
        state = 1 if self.cc_toggles[idx].get() else 0

        if not osc_address.startswith("/"):
            self.log_message(f"Invalid OSC address for CC Toggle #{idx+1}: {osc_address}")
            messagebox.showerror("Invalid OSC Address", f"OSC address for CC Toggle #{idx+1} must start with '/'.")
            return

        if self.osc_client:
            try:
                self.osc_client.send_message(osc_address, state)
                self.log_message(f"Sent OSC to {osc_address} with state {state}")
            except Exception as e:
                self.log_message(f"Failed to send OSC message to {osc_address}: {e}")
        else:
            self.log_message("OSC Client not connected. Cannot send CC Toggle message.")

    # ------------------ OSC Handlers ----------------- #
    def handle_previous(self, address, *args):
        self.previous()

    def handle_numeric_skip(self, address, *args):
        match_obj = re.match(r'^/(\d+)$', address)
        if match_obj:
            num = int(match_obj.group(1))
            self.skip_to_number(num)
        else:
            self.log_message(f"Unhandled numeric OSC address: {address}")

    def handle_bpm1_toggle(self, address, *args):
        current = self.ignore_bpm_var.get()
        new_val = not current
        self.ignore_bpm_var.set(new_val)
        self.log_message(f"'{self.osc_addresses_in['bpm1']}' toggled -> ignoring /bpm = {new_val}")

    def handle_resetbpm(self, address, *args):
        if not self.playing:
            self.log_message("Received /resetbpm but playback not running.")
            return
        self.user_bpm = max(1, round(self.default_bpm))
        self.smoothed_bpm = float(self.user_bpm)
        self.bpm_slider.set(self.user_bpm)
        self.log_message("BPM reset via /resetbpm to current MIDI's default.")

    def handle_pause(self, address, *args):
        if self.playing and not self.pause_event.is_set():
            self.pause_event.set()
            self.info_label.config(text="Playback paused.")
            self.log_message("Playback paused (OSC).")

    def handle_play(self, address, *args):
        if self.playing and self.pause_event.is_set():
            self.pause_event.clear()
            self.info_label.config(text="Playback resumed.")
            self.log_message("Playback resumed (OSC).")

    def handle_skip(self, address, *args):
        if self.playing:
            self.skip_event.set()
            self.log_message("Skip requested (OSC).")
        else:
            self.log_message("Skip but no playback active.")

    def handle_back(self, address, *args):
        if self.playing:
            self.back_event.set()
            self.log_message("Back requested (OSC).")
        else:
            self.log_message("Back but no playback active.")

    def handle_bpm(self, address, *args):
        if self.bpm_locked or self.ignore_bpm_var.get():
            self.log_message(f"Got {address}, but locked or ignored.")
            return
        now = time.time()
        self.bpm_tick_times.append(now)
        if len(self.bpm_tick_times) > 4:
            self.bpm_tick_times.pop(0)
        if len(self.bpm_tick_times) == 4:
            intervals = []
            for i in range(3):
                intervals.append(self.bpm_tick_times[i+1] - self.bpm_tick_times[i])
            avg_interval = sum(intervals) / len(intervals)
            new_bpm = 60.0 / avg_interval
            self.smoothed_bpm = self.alpha * new_bpm + (1 - self.alpha) * self.smoothed_bpm
            final_bpm = max(1, round(self.smoothed_bpm))
            self.user_bpm = final_bpm
            self.master.after(0, lambda: self.bpm_slider.set(final_bpm))
            self.log_message(f"{address} -> {final_bpm}")

    # ----------------- CC Controls ----------------- #
    # These methods are already integrated above with send_cc_message and send_cc_toggle

    # ----------------- MIDI to OSC ----------------- #
    def run_midi_loop(self, midi_in):
        asyncio.set_event_loop(self.loop)
        self.loop.create_task(self.midi_to_osc(midi_in))

    async def midi_to_osc(self, midi_in):
        while True:
            for message in midi_in.iter_pending():
                self.handle_midi_message(message, source='input')
            await asyncio.sleep(0.01)

    # ----------------------- Cleanup ------------------------------ #
    def quit_app(self):
        try:
            if self.midi_out:
                self.midi_out.close()
        except Exception as e:
            print(f"Error closing MIDI out: {e}")
        finally:
            self.playing = False
            self.pause_event.clear()
            self.skip_event.set()
            self.back_event.set()
            self.previous_event.set()
            self.skip_to_event.set()
            self.sync_stop_event.set()
            if self.sync_thread and self.sync_thread.is_alive():
                self.sync_thread.join(timeout=1)
            if self.server_transport:
                self.server_transport.close()
                self.server_transport = None
                self.server_protocol = None
                self.set_connection_status('red')
                self.log_message("OSC Server stopped.")
            self.loop.call_soon_threadsafe(self.loop.stop)
            if hasattr(self, 'loop_thread') and self.loop_thread and self.loop_thread.is_alive():
                self.loop_thread.join(timeout=1)
            self.master.quit()

    # ----------------------- Toggling the 3 frames & auto-resize ------------------------------ #
    def toggle_midi_menu(self):
        # Hide other frames first
        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")

        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")

        # Toggle this one
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")
            self.log_message("MIDI Player/Log UI hidden.")
        else:
            self.content_frame.pack(fill=tk.BOTH, expand=True)
            self.content_visible = True
            self.menu_button.config(text="≡ Hide Midi Player/Log")
            self.log_message("MIDI Player/Log UI shown.")

        self.master.update_idletasks()
        self.master.geometry("")

    def toggle_alarm_menu(self):
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")

        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")

        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")
            self.log_message("Alarm Clock UI hidden.")
        else:
            self.alarm_frame.pack(fill=tk.BOTH, expand=True)
            self.alarm_frame_visible = True
            self.alarm_menu_button.config(text="≡ Hide Alarm Clock")
            self.log_message("Alarm Clock UI shown.")

        self.master.update_idletasks()
        self.master.geometry("")

    def toggle_cc_menu(self):
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")

        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")

        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")
            self.log_message("CC UI hidden.")
        else:
            self.cc_frame.pack(fill=tk.BOTH, expand=True)
            self.cc_frame_visible = True
            self.cc_menu_button.config(text="≡ Hide CC")
            self.log_message("CC UI shown.")

        self.master.update_idletasks()
        self.master.geometry("")

    # ----------------------- CC Controls Integration ------------------------------ #

    # The send_cc_message and send_cc_toggle methods are already integrated above in setup_cc_ui
    # They are bound to the sliders and toggles respectively

    # ----------------------- Main Execution ------------------------------ #

# Create an instance of OSCMIDIApp and run the application
if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("500x350")  # Initial size
    app = OSCMIDIApp(root)
    root.mainloop()
