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

    MAX_LOG_MESSAGES = 50  # Log capacity

    def __init__(self, master):
        self.master = master
        self.master.title("OSC2MIDI - Live Edition (Dark)")

        # --- Dark theme (ttk.Style) ---
        style = ttk.Style(self.master)
        style.theme_use('default')
        style.configure('.',
                        background='#2B2B2B',
                        foreground='#FFFFFF',
                        fieldbackground='#3A3A3A')
        style.configure('TFrame', background='#2B2B2B')
        style.configure('TLabel', background='#2B2B2B', foreground='#FFFFFF')
        style.configure('TButton', background='#3A3A3A', foreground='#FFFFFF')
        style.map('TButton', background=[('active', '#4D4D4D')])
        style.configure('TCheckbutton',
                        background='#2B2B2B',
                        foreground='#FFFFFF')
        style.map('TCheckbutton',
                  background=[('active', '#4D4D4D')])
        style.configure('TEntry',
                        foreground='#FFFFFF',
                        background='#3A3A3A',
                        fieldbackground='#3A3A3A')
        self.master.configure(bg='#2B2B2B')

        # --- Playback/Playlist state ---
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

        # UI frames visibility
        self.content_visible = False   # MIDI/Log
        self.alarm_frame_visible = False  # Alarm

        # Server connection transport and protocol
        self.server_transport = None
        self.server_protocol = None

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
        }
        with open(self.CONFIG_FILE, 'w') as f:
            json.dump(config, f)

    def setup_ui(self):
        self.master.geometry("290x230")  # Start small

        # ------------- Menu Bar ------------- #
        menu_bar = tk.Menu(self.master)
        self.master.config(menu=menu_bar)

        # Add Help Menu
        help_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="OSC Commands", command=self.show_help)

        # ------------- Settings Frame (top area) ------------- #
        settings_frame = ttk.Frame(self.master)
        settings_frame.pack(padx=10, pady=10, fill=tk.X)

        ttk.Label(settings_frame, text="IP for OSC In:").grid(row=0, column=0, sticky=tk.W)
        self.ip_entry = ttk.Entry(settings_frame)
        self.saved_ip = self.get_local_ip()
        self.ip_entry.insert(0, self.saved_ip)
        self.ip_entry.config(state='readonly')
        self.ip_entry.grid(row=0, column=1, sticky=tk.EW)
        Tooltip(self.ip_entry, "Local IP address for OSC server.")

        ttk.Label(settings_frame, text="Port for OSC In:").grid(row=1, column=0, sticky=tk.W)
        self.port_entry = ttk.Entry(settings_frame)
        self.port_entry.insert(0, self.saved_port)
        self.port_entry.grid(row=1, column=1, sticky=tk.EW)
        Tooltip(self.port_entry, "Port number where OSC server listens.")

        ttk.Label(settings_frame, text="Select MIDI Input:").grid(row=2, column=0, sticky=tk.W)
        self.midi_input_combo = ttk.Combobox(settings_frame, values=self.get_midi_ports())
        self.midi_input_combo.set(self.saved_midi_port)
        self.midi_input_combo.grid(row=2, column=1, sticky=tk.EW)
        Tooltip(self.midi_input_combo, "Choose your MIDI input device (optional).")

        ttk.Label(settings_frame, text="Select MIDI Output:").grid(row=3, column=0, sticky=tk.W)
        self.midi_out_combo = ttk.Combobox(settings_frame, values=self.get_midi_output_ports())
        self.midi_out_combo.set(self.saved_midi_out_port)
        self.midi_out_combo.grid(row=3, column=1, sticky=tk.EW)
        Tooltip(self.midi_out_combo, "Choose your MIDI output device (optional).")

        ttk.Label(settings_frame, text="IP for OSC Out:").grid(row=4, column=0, sticky=tk.W)
        self.output_ip_entry = ttk.Entry(settings_frame)
        self.output_ip_entry.insert(0, self.saved_out_ip)
        self.output_ip_entry.grid(row=4, column=1, sticky=tk.EW)
        Tooltip(self.output_ip_entry, "Destination IP address for OSC messages.")

        ttk.Label(settings_frame, text="Port for OSC Out:").grid(row=5, column=0, sticky=tk.W)
        self.output_port_entry = ttk.Entry(settings_frame)
        self.output_port_entry.insert(0, self.saved_out_port)
        self.output_port_entry.grid(row=5, column=1, sticky=tk.EW)
        Tooltip(self.output_port_entry, "Destination port for OSC messages.")

        # NEW: Shared Socket ID (1-4)
        ttk.Label(settings_frame, text="Shared Socket ID:").grid(row=6, column=0, sticky=tk.W)
        self.shared_socket_combo = ttk.Combobox(settings_frame, values=["1", "2", "3", "4"], width=5)
        self.shared_socket_combo.current(0)  # Default to "1"
        self.shared_socket_combo.grid(row=6, column=1, sticky=tk.EW)
        Tooltip(self.shared_socket_combo, "Pick 1-4 if you want multiple apps to share the same port.\nAll must set the same port & enable SO_REUSEPORT for it to work.")

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
        # Draw the circle, initial red
        self.indicator = self.connection_indicator.create_oval(5, 5, 15, 15, fill='red')

        # ------ Frame for Burger Menus side-by-side ------
        burger_frame = ttk.Frame(self.master)
        burger_frame.pack(pady=2)

        # ------------- Burger Menu 1 (MIDI Player/Log) ------------- #
        self.menu_button = ttk.Button(burger_frame, text="≡ Midi Player/Log", command=self.toggle_midi_menu, width=17)
        self.menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.menu_button, "Show/Hide MIDI Player and Log UI.")

        # ------------- Burger Menu 2 (Alarm Clock) ------------- #
        self.alarm_menu_button = ttk.Button(burger_frame, text="≡ Alarm Clock", command=self.toggle_alarm_menu, width=17)
        self.alarm_menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.alarm_menu_button, "Show/Hide the Alarm Clock scheduling UI.")

        # ------------- Content Frame (MIDI/Log) ------------- #
        self.content_frame = ttk.Frame(self.master)  # hidden initially
        self.setup_midi_ui()

        # ------------- Alarm Frame (Scheduling) ------------- #
        self.alarm_frame = ttk.Frame(self.master)  # hidden initially
        self.setup_alarm_ui()

        self.load_bottom_logo()

    def setup_midi_ui(self):
        """
        Build out widgets for the MIDI player, logs, BPM, playlist, etc.
        This content is toggled by self.menu_button.
        """
        # Controls Frame
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

        # File Controls Frame
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

        # Playback Options Frame
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

        # Sync BPM Checkbutton
        self.sync_checkbutton = ttk.Checkbutton(
            playback_options_frame,
            text="Sync BPM",
            variable=self.sync_var,
            command=self.toggle_sync
        )
        self.sync_checkbutton.pack(side=tk.LEFT, padx=5)
        Tooltip(self.sync_checkbutton, "Enable or disable sending /sync messages.")

        # Info Label
        self.info_label = tk.Label(self.content_frame, text="No file loaded", fg="#FFFFFF", bg="#2B2B2B")
        self.info_label.pack(pady=5)

        # BPM Frame
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

        self.lock_bpm_button = ttk.Button(bpm_frame, text="Lock Tempo", command=self.toggle_lock_bpm)
        self.lock_bpm_button.pack(side=tk.LEFT, padx=5)

        self.ignore_bpm_checkbox = ttk.Checkbutton(
            bpm_frame,
            text="Ignore /bpm",
            variable=self.ignore_bpm_var,
            command=self.toggle_ignore_bpm
        )
        self.ignore_bpm_checkbox.pack(side=tk.LEFT, padx=5)

        # Log Frame
        tk.Label(self.content_frame, text="Log Messages:", bg='#2B2B2B', fg='#FFFFFF').pack()
        log_frame = ttk.Frame(self.content_frame)
        log_frame.pack()
        self.log_text = tk.Text(
            log_frame,
            height=8,
            width=70,
            state='disabled',
            bg='#1E1E1E',
            fg='#FFFFFF',
            insertbackground='#FFFFFF'
        )
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        log_scroll = ttk.Scrollbar(log_frame, command=self.log_text.yview)
        self.log_text.config(yscrollcommand=log_scroll.set)
        log_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        # Playlist Frame
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
            height=15
        )
        self.playlist_box.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        playlist_scroll = ttk.Scrollbar(playlist_frame, command=self.playlist_box.yview)
        self.playlist_box.config(yscrollcommand=playlist_scroll.set)
        playlist_scroll.pack(side=tk.RIGHT, fill=tk.Y)

    def setup_alarm_ui(self):
        """
        Creates the widgets used to schedule and display alarms.
        """
        # Current time display
        time_frame = ttk.Frame(self.alarm_frame)
        time_frame.pack(pady=5, fill=tk.X)
        self.clock_label = tk.Label(time_frame, text="Current Time: --:--:--", bg="#2B2B2B", fg="#FFFFFF")
        self.clock_label.pack(side=tk.LEFT, padx=5)

        # Alarm Scheduling Frame
        schedule_frame = ttk.Frame(self.alarm_frame)
        schedule_frame.pack(pady=5, fill=tk.X)

        # Compute default date/time = now + 2 minutes
        now = datetime.now()
        default_date_str = now.strftime("%Y-%m-%d")
        default_time_str = (now + timedelta(minutes=2)).strftime("%H:%M:%S")  # with seconds

        ttk.Label(schedule_frame, text="Date (YYYY-MM-DD):").grid(row=0, column=0, sticky=tk.W, padx=5)
        self.alarm_date_entry = ttk.Entry(schedule_frame, width=12)
        self.alarm_date_entry.grid(row=0, column=1, sticky=tk.W, padx=5)
        self.alarm_date_entry.insert(0, default_date_str)

        ttk.Label(schedule_frame, text="Time (HH:MM:SS):").grid(row=1, column=0, sticky=tk.W, padx=5)
        self.alarm_time_entry = ttk.Entry(schedule_frame, width=10)
        self.alarm_time_entry.grid(row=1, column=1, sticky=tk.W, padx=5)
        self.alarm_time_entry.insert(0, default_time_str)

        ttk.Label(schedule_frame, text="OSC Address:").grid(row=2, column=0, sticky=tk.W, padx=5)
        self.alarm_address_entry = ttk.Entry(schedule_frame, width=20)
        self.alarm_address_entry.grid(row=2, column=1, sticky=tk.W, padx=5)
        self.alarm_address_entry.insert(0, "/clock")  # default

        ttk.Label(schedule_frame, text="OSC Args:").grid(row=3, column=0, sticky=tk.W, padx=5)
        self.alarm_args_entry = ttk.Entry(schedule_frame, width=20)
        self.alarm_args_entry.grid(row=3, column=1, sticky=tk.W, padx=5)
        self.alarm_args_entry.insert(0, "1.0")  # default float

        self.schedule_alarm_button = ttk.Button(schedule_frame, text="Schedule Alarm", command=self.schedule_alarm)
        self.schedule_alarm_button.grid(row=4, column=0, columnspan=2, pady=5)

        # Alarms List
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

        # Remove alarm
        self.remove_alarm_button = ttk.Button(self.alarm_frame, text="Remove Selected Alarm", command=self.remove_selected_alarm)
        self.remove_alarm_button.pack(pady=5)

    # ------------------ Menu Handlers ------------------ #
    def show_help(self):
        help_window = tk.Toplevel(self.master)
        help_window.title("Help - OSC Commands")
        help_window.geometry("500x600")
        help_window.resizable(False, False)

        # Make it modal
        help_window.transient(self.master)
        help_window.grab_set()

        # Create a Text widget to display commands
        text = tk.Text(help_window, wrap='word', bg='#2B2B2B', fg='#FFFFFF', font=("Courier", 10))
        text.pack(expand=True, fill='both', padx=10, pady=10)

        # Insert the OSC commands
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

    # ------------------ Burger Menus / Toggling  ------------------ #
    def toggle_midi_menu(self):
        """
        If the alarm menu is open, close it. Then toggle MIDI/Log.
        """
        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")

        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")
            self.master.geometry("290x230")
            self.log_message("MIDI/Log Menu hidden.")
        else:
            self.content_frame.pack(pady=5)
            self.content_visible = True
            self.menu_button.config(text="✕ Midi Player/Log")
            self.master.geometry("475x675")
            self.log_message("MIDI/Log Menu shown.")

    def toggle_alarm_menu(self):
        """
        If the MIDI/Log menu is open, close it. Then toggle alarm frame.
        """
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")

        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")
            self.master.geometry("290x230")
            self.log_message("Alarm Clock Menu hidden.")
        else:
            self.alarm_frame.pack(pady=5)
            self.alarm_frame_visible = True
            self.alarm_menu_button.config(text="✕ Alarm Clock")
            self.master.geometry("475x675")
            self.log_message("Alarm Clock Menu shown.")

    # ---------------------- Alarms ---------------------- #
    def schedule_alarm(self):
        date_str = self.alarm_date_entry.get().strip()
        time_str = self.alarm_time_entry.get().strip()  # now "HH:MM:SS"
        address = self.alarm_address_entry.get().strip()
        args_str = self.alarm_args_entry.get().strip()

        if not date_str or not time_str or not address:
            messagebox.showwarning("Incomplete Data", "Please enter Date, Time (HH:MM:SS), and OSC Address.")
            return

        # Parse datetime with seconds
        try:
            alarm_datetime = datetime.strptime(f"{date_str} {time_str}", "%Y-%m-%d %H:%M:%S")
        except ValueError:
            messagebox.showwarning("Invalid Date/Time", "Use YYYY-MM-DD and HH:MM:SS (24-hour).")
            return

        # Parse args
        args = args_str.split() if args_str else []

        alarm_entry = {
            "datetime": alarm_datetime,
            "address": address,
            "args": args,
            "triggered": False
        }
        self.alarms.append(alarm_entry)
        display_text = f"{alarm_datetime} -> {address} {' '.join(args)}"
        self.alarm_listbox.insert(tk.END, display_text)

        self.log_message(f"Scheduled alarm at {alarm_datetime}, address={address}, args={args}")

        # ---- Reload default fields right after scheduling ----
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

    # ------------------ BPM / Playback / Playlist  ------------------ #
    def display_osc_addresses(self):
        self.log_message("------ OSC Addresses ------")
        self.log_message("Incoming OSC Addresses:")
        incoming_addresses = {
            "/pause": "Pause playback.",
            "/play": "Resume playback.",
            "/skip": "Skip to next track.",
            "/back": "Restart current track.",
            "/previous": "Return to previous track.",
            "/bpm": "Set BPM via OSC.",
            "/bpm1": "Toggle ignoring BPM sync.",
            "/resetbpm": "Reset BPM to song's default.",
            "/1 - /50": "Load specific song.",
        }
        for addr, desc in incoming_addresses.items():
            self.log_message(f"  {addr}: {desc}")

        self.log_message("Outgoing OSC Addresses:")
        self.log_message("  /sync: Sent periodically with BPM value.")
        self.log_message("  /chXnote, /chXnvalue, /chXnoteoff, /chXnoffvalue, /chXcc, /chXccvalue, /chXpitch, /chXpressure (X=1..16)")
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
                self.osc_client.send_message("/sync", current_bpm)
                self.log_message(f"Sent /sync at BPM {current_bpm}")

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
        self.log_text.config(state="normal")
        self.log_text.delete("1.0", tk.END)
        self.log_text.config(state="disabled")

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

            # Close OSC server
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

                # Handling special events
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

                # Loop or next
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
                # Close OSC server after playback finishes
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
        abs_ticks = 0
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
        """
        Forward relevant MIDI -> OSC.
        Split Control Change messages into /chXcc and /chXccvalue.
        """
        if hasattr(message, 'channel'):
            ch = message.channel + 1
            if message.type in ('note_on', 'note_off'):
                note = message.note
                velocity = message.velocity
                if source == 'playback':
                    if message.type == 'note_on' and velocity > 0:
                        if self.osc_client:
                            self.osc_client.send_message(f"/ch{ch}note", note)
                        self.log_message(f"Playback -> /ch{ch}note {note}")
                    else:
                        self.log_message(f"Playback -> Skipping note_off: {note}")
                else:
                    if self.osc_client:
                        if message.type == 'note_on' and velocity > 0:
                            self.osc_client.send_message(f"/ch{ch}note", note)
                            self.osc_client.send_message(f"/ch{ch}nvalue", velocity)
                        else:
                            self.osc_client.send_message(f"/ch{ch}noteoff", note)
                            self.osc_client.send_message(f"/ch{ch}noffvalue", 0)
                    if message.type == 'note_on' and velocity > 0:
                        self.log_message(f"Input -> /ch{ch}note {note}")
                        self.log_message(f"Input -> /ch{ch}nvalue {velocity}")
                    else:
                        self.log_message(f"Input -> /ch{ch}noteoff {note}")
                        self.log_message(f"Input -> /ch{ch}noffvalue 0")
            elif message.type == 'control_change':
                cc_number = message.control
                cc_value = message.value
                if self.osc_client:
                    # Send /chXcc with CC number (int 0-127)
                    self.osc_client.send_message(f"/ch{ch}cc", cc_number)
                    self.log_message(f"Input -> /ch{ch}cc {cc_number}")

                    # Send /chXccvalue with CC value scaled to float 0-1
                    scaled_value = cc_value / 127.0
                    self.osc_client.send_message(f"/ch{ch}ccvalue", float(scaled_value))
                    self.log_message(f"Input -> /ch{ch}ccvalue {scaled_value:.3f}")
            elif message.type == 'pitchwheel':
                if self.osc_client:
                    osc_address = f"/ch{ch}pitch"
                    self.osc_client.send_message(osc_address, message.pitch)
                if source == 'input':
                    self.log_message(f"Input -> /ch{ch}pitch {message.pitch}")
            elif message.type == 'aftertouch':
                if self.osc_client:
                    osc_address = f"/ch{ch}pressure"
                    self.osc_client.send_message(osc_address, message.value)
                if source == 'input':
                    self.log_message(f"Input -> /ch{ch}pressure {message.value}")
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
        """
        Allows starting the OSC server without requiring a MIDI input.
        If no MIDI selected, just warn user but proceed.
        """
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
                messagebox.showwarning("No MIDI In", "No MIDI input selected. MIDI features may be unavailable.")
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
            # (We allow multiple processes to share via SO_REUSEPORT if the OS supports it.)
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
        """
        Create and bind a shared socket manually with SO_REUSEPORT
        (if supported by the OS). This allows multiple apps to receive
        the same incoming OSC messages on the same port.
        """
        disp = dispatcher.Dispatcher()
        disp.map("/pause", self.handle_pause)
        disp.map("/play", self.handle_play)
        disp.map("/skip", self.handle_skip)
        disp.map("/back", self.handle_back)
        disp.map("/previous", self.handle_previous)
        disp.map("/bpm", self.handle_bpm)
        disp.map("/bpm1", self.handle_bpm1_toggle)
        disp.map("/resetbpm", self.handle_resetbpm)

        for i in range(1, 51):
            disp.map(f"/{i}", self.handle_numeric_skip)

        # Create a UDP socket ourselves to set SO_REUSEPORT
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        # Allow re-bind if the OS supports it
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
            self.log_message("SO_REUSEPORT enabled (your OS must support it).")
        except AttributeError:
            # SO_REUSEPORT might not be available on all systems
            self.log_message("SO_REUSEPORT not available on this platform.")

        # 0.0.0.0 means all interfaces
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
            None,   # let python-osc skip its own bind
            disp,
            self.loop,
            sock=sock  # supply our shared socket
        )
        transport, protocol = await server.create_serve_endpoint()
        self.server_transport = transport
        self.server_protocol = protocol
        self.log_message(f"Async OSC Server started on port {port} with shared socket.")

    def set_connection_status(self, color):
        if color not in ['red', 'green']:
            color = 'red'
        self.master.after(0, lambda: self.connection_indicator.itemconfig(self.indicator, fill=color))

    # ----------------- OSC Handlers ----------------- #
    def handle_previous(self, address, *args):
        self.previous()

    def handle_numeric_skip(self, address, *args):
        match = re.match(r'^/(\d+)$', address)
        if match:
            num = int(match.group(1))
            self.skip_to_number(num)
        else:
            self.log_message(f"Unhandled numeric OSC address: {address}")

    def handle_bpm1_toggle(self, address, *args):
        current = self.ignore_bpm_var.get()
        new_val = not current
        self.ignore_bpm_var.set(new_val)
        self.log_message(f"'/bpm1' toggled -> ignoring /bpm = {new_val}")

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
            self.log_message("Got /bpm, but locked or ignored.")
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
            self.log_message(f"/bpm -> {final_bpm}")

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
            # Close OSC server
            if self.server_transport:
                self.server_transport.close()
                self.server_transport = None
                self.server_protocol = None
                self.set_connection_status('red')
                self.log_message("OSC Server stopped.")
            self.loop.call_soon_threadsafe(self.loop.stop)
            if self.loop_thread and self.loop_thread.is_alive():
                self.loop_thread.join(timeout=1)
            self.master.quit()

    # ----------------------- Main Execution ------------------------------ #
if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("210x210")  # Start with a small window size
    app = OSCMIDIApp(root)
    root.protocol("WM_DELETE_WINDOW", app.quit_app)
    root.mainloop()
