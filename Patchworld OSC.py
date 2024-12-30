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

# --------------------- Tooltip Class Definition --------------------- #
class Tooltip:
    """
    Creates a tooltip for a given widget as the mouse hovers over it.

    Usage:
        tooltip = Tooltip(widget, "Your tooltip text")
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
        tw.wm_overrideredirect(True)  # Remove all window decorations
        tw.wm_geometry(f"+{self.widget.winfo_rootx()+20}+{self.widget.winfo_rooty()+20}")
        # Create a label inside the Toplevel
        label = tk.Label(tw, text=self.text, justify='left',
                         background="#333333", foreground="#FFFFFF",
                         relief='solid', borderwidth=1,
                         font=("tahoma", "8", "normal"))
        label.pack(ipadx=1)

    def hide_tooltip(self, event=None):
        tw = self.tooltip_window
        self.tooltip_window = None
        if tw:
            tw.destroy()

# ----------------------- OSCMIDIApp Class ---------------------------- #
class OSCMIDIApp:
    CONFIG_FILE = "config.json"

    MAX_LOG_MESSAGES = 50  # Set to 50 as per user request

    def __init__(self, master):
        self.master = master
        self.master.title("OSC2MIDI - Live Edition (Dark)")

        # -- Dark theme styling (ttk.Style) --
        style = ttk.Style(self.master)
        style.theme_use('default')

        style.configure('.',
                        background='#2B2B2B',    # Dark background
                        foreground='#FFFFFF',   # White text
                        fieldbackground='#3A3A3A')
        style.configure('TFrame',
                        background='#2B2B2B')
        style.configure('TLabel',
                        background='#2B2B2B',
                        foreground='#FFFFFF')
        style.configure('TButton',
                        background='#3A3A3A',
                        foreground='#FFFFFF')
        style.map('TButton',
                  background=[('active', '#4D4D4D')])
        style.configure('TCheckbutton',
                        background='#2B2B2B',
                        foreground='#FFFFFF')
        style.map('TCheckbutton',
                  background=[('active', '#4D4D4D')])
        style.configure('TEntry',
                        foreground='#FFFFFF',
                        background='#3A3A3A',
                        fieldbackground='#3A3A3A')

        # Force the master background to match
        self.master.configure(bg='#2B2B2B')

        # Playback / Playlist state
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

        # For skipping to a specific index
        self.skip_to_event = threading.Event()
        self.skip_to_index = None

        # BPM and tempo
        self.default_bpm = 120.0
        self.user_bpm = 120.0
        self.ticks_per_beat = 480

        # For /bpm auto-detection (last 4 ticks)
        self.bpm_tick_times = []

        # Exponential Moving Average (EMA) for smoothing BPM
        self.alpha = 0.2
        self.smoothed_bpm = self.default_bpm

        # BPM Lock state
        self.bpm_locked = False

        # Ignore /bpm checkbox (enabled by default)
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
        # Guarantee the user_bpm matches the slider
        self.loop = asyncio.new_event_loop()
        self.midi_queue = asyncio.Queue()
        self.active_notes = {}

        # OSC Server
        self.osc_server_task = None
        self.loop_thread = None

        # Load icon (optional)
        self.load_icon()

        # Load config
        self.load_config()

        # Build UI
        self.setup_ui()

        # Display initial OSC addresses in the log
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
                # Set osc_out_ip to osc_in_ip by default if not specified
                self.saved_out_ip = config.get("osc_out_ip", self.get_local_ip())
                self.saved_out_port = config.get("osc_out_port", "3330")
        else:
            self.saved_port = "3330"
            self.saved_midi_port = ""
            self.saved_midi_out_port = ""
            self.saved_out_ip = self.get_local_ip()  # Default to local IP
            self.saved_out_port = "5550"

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
        # Set initial window size to small (200x200)
        self.master.geometry("275x210")  # Width x Height

        # Settings Frame
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
        Tooltip(self.midi_input_combo, "Choose your MIDI input device.")

        ttk.Label(settings_frame, text="Select MIDI Output:").grid(row=3, column=0, sticky=tk.W)
        self.midi_out_combo = ttk.Combobox(settings_frame, values=self.get_midi_output_ports())
        self.midi_out_combo.set(self.saved_midi_out_port)
        self.midi_out_combo.grid(row=3, column=1, sticky=tk.EW)
        Tooltip(self.midi_out_combo, "Choose your MIDI output device.")

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

        settings_frame.columnconfigure(1, weight=1)

        # Start Server Button
        self.start_button = ttk.Button(self.master, text="Start Server", command=self.start)
        self.start_button.pack(pady=5)
        Tooltip(self.start_button, "Start or stop the OSC server and MIDI input.")

        # Burger Menu Button with Text
        self.menu_button = ttk.Button(self.master, text="≡ Midi Player/Log", command=self.toggle_menu, width=20)
        self.menu_button.pack(pady=2)
        Tooltip(self.menu_button, "Show/Hide additional settings and controls.")

        # Content Frame (holds all other UI elements)
        self.content_frame = ttk.Frame(self.master)
        # Initially hidden
        self.content_visible = False

        # Now, create and pack all other frames inside content_frame
        # Controls Frame
        controls_frame = ttk.Frame(self.content_frame)
        controls_frame.pack(pady=5)

        self.play_button = ttk.Button(controls_frame, text="Play", command=self.play)
        self.play_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.play_button, "Start playback of the playlist.")

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
        Tooltip(self.previous_button, "Load the previously loaded MIDI file.")

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
        Tooltip(self.looping_checkbutton, "Enable or disable looping of the playlist.")

        # Randomize button
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
        Tooltip(self.sync_checkbutton, "Enable or disable sending /sync OSC messages based on BPM.")

        # Info Label
        self.info_label = tk.Label(self.content_frame, text="No file loaded", fg="#FFFFFF", bg="#2B2B2B")
        self.info_label.pack(pady=5)
        Tooltip(self.info_label, "Displays current status and loaded files.")

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
        Tooltip(self.bpm_slider, "Adjust the tempo in BPM. This affects the /sync messages if Sync BPM is enabled.")

        self.reset_bpm_button = ttk.Button(bpm_frame, text="Reset Tempo", command=self.reset_bpm)
        self.reset_bpm_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.reset_bpm_button, "Reset the tempo slider to the default BPM.")

        self.lock_bpm_button = ttk.Button(bpm_frame, text="Lock Tempo", command=self.toggle_lock_bpm)
        self.lock_bpm_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.lock_bpm_button, "Lock or unlock the tempo slider to prevent changes.")

        self.ignore_bpm_checkbox = ttk.Checkbutton(
            bpm_frame,
            text="Ignore /bpm",
            variable=self.ignore_bpm_var,
            command=self.toggle_ignore_bpm
        )
        self.ignore_bpm_checkbox.pack(side=tk.LEFT, padx=5)
        Tooltip(self.ignore_bpm_checkbox, "Ignore incoming /bpm OSC messages.")

        # Log Frame
        tk.Label(self.content_frame, text="Log Messages:", bg='#2B2B2B', fg='#FFFFFF').pack()
        log_frame = ttk.Frame(self.content_frame)
        log_frame.pack()
        self.log_text = tk.Text(
            log_frame,
            height=8,  # Increased from 10 to 15
            width=70,
            state='disabled',
            bg='#1E1E1E',
            fg='#FFFFFF',
            insertbackground='#FFFFFF'
        )
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        Tooltip(self.log_text, "Displays log messages and status updates.")

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
            height=15  # Increased height
        )
        self.playlist_box.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        Tooltip(self.playlist_box, "Displays the list of loaded MIDI files.")

        playlist_scroll = ttk.Scrollbar(playlist_frame, command=self.playlist_box.yview)
        self.playlist_box.config(yscrollcommand=playlist_scroll.set)
        playlist_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.load_bottom_logo()

    def toggle_menu(self):
        """
        Toggles the visibility of the content_frame and adjusts the window size accordingly.
        """
        if self.content_visible:
            self.content_frame.pack_forget()
            self.content_visible = False
            self.menu_button.config(text="≡ Midi Player/Log")
            self.master.geometry("250x210")  # Shrink window
            self.log_message("Menu hidden.")
        else:
            self.content_frame.pack(pady=5)
            self.content_visible = True
            self.menu_button.config(text="✕ Midi Player/Log")
            self.master.geometry("475x675")  # Expand window
            self.log_message("Menu shown.")

    def display_osc_addresses(self):
        """
        Logs all incoming and outgoing OSC addresses to help users set up the OSC server correctly.
        Summarized for clarity.
        """
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
        self.log_message("  /chXnote, /chXnvalue, /chXnoteoff, /chXnoffvalue, /chXccY, /chXpitch, /chXpressure (X=1..16)")
        self.log_message("------------------------------")

    # --------------------- SYNC BPM FEATURES --------------------------- #
    def toggle_sync(self):
        """
        Called whenever the "Sync BPM" checkbox changes.
        Starts or stops sending /sync messages based on self.user_bpm.
        """
        if self.sync_var.get():
            # Start sync thread if not already running
            if not self.sync_thread or not self.sync_thread.is_alive():
                self.sync_stop_event.clear()
                self.sync_thread = threading.Thread(target=self._sync_loop, daemon=True)
                self.sync_thread.start()
                self.log_message("Sync BPM started.")
        else:
            # Stop syncing
            if self.sync_thread and self.sync_thread.is_alive():
                self.sync_stop_event.set()
                self.log_message("Sync BPM stopped.")

    def _sync_loop(self):
        """
        Continuously sends OSC /sync messages at intervals based on self.user_bpm,
        even if playback isn't active.
        """
        while not self.sync_stop_event.is_set() and self.sync_var.get():
            current_bpm = max(1, round(self.user_bpm))
            interval = 60.0 / current_bpm
            time.sleep(interval)

            if self.sync_stop_event.is_set() or not self.sync_var.get():
                break

            if self.osc_client:
                self.osc_client.send_message("/sync", current_bpm)
                self.log_message(f"Sent /sync at BPM {current_bpm}")

    # ------------------------------------------------------------------ #

    def log_message(self, message: str):
        # Enforce max log messages = 50
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
        """
        Called whenever the BPM slider changes.
        1) Smoothing via alpha
        2) Rounding to int
        3) Guarantee slider & self.user_bpm match
        """
        if self.bpm_locked:
            return
        try:
            new_bpm = float(new_bpm_str)
            self.smoothed_bpm = self.alpha * new_bpm + (1 - self.alpha) * self.smoothed_bpm
            final_bpm = max(1, round(self.smoothed_bpm))
            self.user_bpm = final_bpm
            # Ensure the slider reflects user_bpm
            self.bpm_slider.set(final_bpm)
            self.log_message(f"User BPM set to {final_bpm}")
        except ValueError:
            pass
    def load_bottom_logo(self):
        """
        Load bottomlogo.ico into a label or as part of the UI.
        """
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
            self.log_message("Incoming /bpm OSC messages are now being processed.")

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
                self.log_message(f"Loaded {len(midi_files)} MIDI files from folder: {folder_path}")
            else:
                messagebox.showinfo("No MIDI Files", "No MIDI files found.")
                self.log_message("No MIDI files found in the selected folder.")
        else:
            self.info_label.config(text="No folder selected.")
            self.log_message("No folder selected.")

    def play(self):
        if not self.playlist:
            self.info_label.config(text="No MIDI files loaded.")
            self.log_message("No MIDI files for playback.")
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

            # Stop sync if running
            if self.sync_thread and self.sync_thread.is_alive():
                self.sync_stop_event.set()
                self.log_message("Sync BPM stopped (playback stopped).")
        else:
            self.log_message("Stop command but playback wasn't running.")

    def skip(self):
        if self.playing:
            self.skip_event.set()
            self.log_message("Skip requested.")
        else:
            self.log_message("Skip but no playback running.")

    def back(self):
        """
        Restarts the current file from the beginning.
        """
        if self.playing:
            self.back_event.set()
            self.log_message("Back requested (Restart current file).")
        else:
            self.log_message("Back but no playback running.")

    def previous(self):
        """
        Loads the previously loaded MIDI file in the playlist, if one exists.
        """
        if self.playing:
            if self.current_index > 0:
                self.previous_event.set()
                self.log_message("Previous requested (Load previous file).")
            else:
                self.log_message("Already at the first file. Cannot go to previous.")
        else:
            self.log_message("Previous but no playback running.")

    def skip_to_number(self, num):
        if not self.playing:
            self.log_message(f"Skip to {num}, but no playback.")
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
        """
        Triggered by a button instead of a checkbox.
        """
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
            # Restore the original playlist order
            self.playlist = self.original_playlist.copy()
            self.update_playlist_box()
            self.current_index = 0
            self.log_message("Playlist order restored to original.")

        # Update button text
        if self.randomize:
            self.randomize_button.config(text="Restore Order")
        else:
            self.randomize_button.config(text="Randomize Playlist")

    def update_playlist_box(self):
        self.playlist_box.delete(0, tk.END)
        for idx, file in enumerate(self.playlist, start=1):
            display_text = f"{idx}: {os.path.basename(file)}"
            self.playlist_box.insert(tk.END, display_text)

    def _play_midi_playlist(self):
        try:
            while self.playing and (0 <= self.current_index < len(self.playlist)):
                midi_file_path = self.playlist[self.current_index]
                self._play_single_midi(midi_file_path)

                if not self.playing:
                    break

                # Check "previous" first
                if self.previous_event.is_set():
                    self.previous_event.clear()
                    self.current_index = max(0, self.current_index - 1)
                    self.log_message("Previous requested, loading previous file.")
                    continue

                # If "back" is set, replay the same file
                if self.back_event.is_set():
                    self.back_event.clear()
                    self.log_message("Back requested, replaying current file.")
                    continue

                if self.skip_to_event.is_set():
                    self.skip_to_event.clear()
                    if self.skip_to_index is not None:
                        if 0 <= self.skip_to_index < len(self.playlist):
                            self.current_index = self.skip_to_index
                            self.log_message(f"Jumping to file #{self.current_index + 1}")
                        else:
                            self.log_message(f"Skip to {self.skip_to_index + 1} is out of range.")
                        self.skip_to_index = None
                    continue

                if self.looping and self.current_index == len(self.playlist) - 1:
                    if self.randomize and len(self.playlist) > 1:
                        random.shuffle(self.playlist)
                        self.update_playlist_box()
                        self.log_message("Playlist reshuffled for looping.")
                    self.current_index = 0
                    self.log_message("Looping. Restarting playlist.")
                else:
                    self.current_index += 1

            if self.playing:
                self.playing = False
                self.info_label.config(text="Playback finished.")
                self.log_message("Playback finished.")
        except Exception as e:
            self.playing = False
            self.log_message(f"Error: {e}")
            self.info_label.config(text=f"Error: {e}")

    def _play_single_midi(self, midi_file_path):
        self.info_label.config(text=f"Playing: {midi_file_path}")
        self.log_message(f"Playing MIDI file: {midi_file_path}")

        try:
            midi_file = MidiFile(midi_file_path)
        except Exception as e:
            self.log_message(f"Failed to load MIDI file: {e}")
            return

        if not self.bpm_locked:
            bpm = self.get_file_bpm(midi_file)
            if bpm:
                # Round to whole number
                self.default_bpm = max(1, round(bpm))
                self.smoothed_bpm = float(self.default_bpm)
                self.user_bpm = self.default_bpm
                self.master.after(0, lambda: self.bpm_slider.set(self.user_bpm))
                self.log_message(f"Default BPM set to {self.default_bpm}")
            else:
                self.log_message("No BPM found in MIDI file. Using existing BPM.")

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
                self.log_message("Skipping next file.")
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
                        self.osc_client.send_message(f"/ch{ch}note", note)
                        self.log_message(f"Playback -> /ch{ch}note {note}")
                    else:
                        self.log_message(f"Playback -> Skipping /ch{ch}noteoff for note {note}")
                else:
                    if message.type == 'note_on' and velocity > 0:
                        self.osc_client.send_message(f"/ch{ch}note", note)
                        self.osc_client.send_message(f"/ch{ch}nvalue", velocity)
                        self.log_message(f"Input -> /ch{ch}note {note}")
                        self.log_message(f"Input -> /ch{ch}nvalue {velocity}")
                    else:
                        self.osc_client.send_message(f"/ch{ch}noteoff", note)
                        self.osc_client.send_message(f"/ch{ch}noffvalue", 0)
                        self.log_message(f"Input -> /ch{ch}noteoff {note}")
                        self.log_message(f"Input -> /ch{ch}noffvalue 0")
            elif message.type == 'control_change':
                if source == 'playback':
                    self.log_message(f"Playback -> Skipping /ch{ch}cc{message.control}")
                else:
                    osc_address = f"/ch{ch}cc{message.control}"
                    self.osc_client.send_message(osc_address, message.value)
                    self.log_message(f"Input -> {osc_address} {message.value}")
            elif message.type == 'pitchwheel':
                if source == 'playback':
                    self.log_message(f"Playback -> Skipping /ch{ch}pitch")
                else:
                    osc_address = f"/ch{ch}pitch"
                    self.osc_client.send_message(osc_address, message.pitch)
                    self.log_message(f"Input -> {osc_address} {message.pitch}")
            elif message.type == 'aftertouch':
                osc_address = f"/ch{ch}pressure"
                self.osc_client.send_message(osc_address, message.value)
                if source == 'playback':
                    self.log_message(f"Playback -> {osc_address} {message.value}")
                else:
                    self.log_message(f"Input -> {osc_address} {message.value}")
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

            if not midi_input_port_name:
                messagebox.showerror("Error", "Select a MIDI input port.")
                return
            if not midi_output_port_name:
                messagebox.showerror("Error", "Select a MIDI output port.")
                return
            if self.is_port_in_use(osc_in_port):
                messagebox.showerror("Error", f"Port {osc_in_port} is in use.")
                return

            # Open MIDI out
            try:
                self.midi_out = mido.open_output(midi_output_port_name)
            except (IOError, ValueError) as e:
                messagebox.showerror("MIDI Error", f"Could not open MIDI output: {e}")
                return

            # Open MIDI in
            try:
                midi_in = mido.open_input(midi_input_port_name)
            except (IOError, ValueError) as e:
                messagebox.showerror("MIDI Error", f"Could not open MIDI input: {e}")
                return

            self.osc_client = udp_client.SimpleUDPClient(osc_out_ip, osc_out_port)

            # Start OSC server using asyncio
            self.osc_server_task = asyncio.run_coroutine_threadsafe(
                self.start_osc_server_async(osc_in_port),
                self.loop
            )
            # Start the event loop in a separate thread if not already running
            if not self.loop.is_running():
                self.loop_thread = threading.Thread(target=self.loop.run_forever, daemon=True)
                self.loop_thread.start()

            # Start MIDI input handling
            self.midi_in_thread = threading.Thread(target=self.run_midi_loop, args=(midi_in,), daemon=True)
            self.midi_in_thread.start()

            # Save settings
            self.saved_out_ip = osc_out_ip
            self.saved_out_port = osc_out_port
            self.saved_port = osc_in_port
            self.saved_midi_port = midi_input_port_name
            self.saved_midi_out_port = midi_output_port_name
            self.save_config()

            self.start_button.config(text="Stop and Quit")
            self.log_message("OSC Server and MIDI Input started.")
        else:
            self.quit_app()

    async def start_osc_server_async(self, port):
        disp = dispatcher.Dispatcher()
        disp.map("/pause", self.handle_pause)
        disp.map("/play", self.handle_play)
        disp.map("/skip", self.handle_skip)
        disp.map("/back", self.handle_back)
        disp.map("/previous", self.handle_previous)  # Handle /previous OSC message
        disp.map("/bpm", self.handle_bpm)
        disp.map("/bpm1", self.handle_bpm1_toggle)
        disp.map("/resetbpm", self.handle_resetbpm)

        # Map numeric addresses /1, /2, /3 ... /50 for direct playlist selection
        for i in range(1, 51):
            disp.map(f"/{i}", self.handle_numeric_skip)

        server = osc_server.AsyncIOOSCUDPServer(("0.0.0.0", port), disp, self.loop)
        transport, protocol = await server.create_serve_endpoint()
        self.log_message(f"Async OSC Server started on port {port}.")

    # ----------------- OSC Handlers ----------------- #
    def handle_previous(self, address, *args):
        """
        Triggers the same logic as pressing the "Previous" button.
        """
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
        if new_val:
            self.log_message("'/bpm1' toggled ON: ignoring /bpm now.")
        else:
            self.log_message("'/bpm1' toggled OFF: processing /bpm now.")

    def handle_resetbpm(self, address, *args):
        if not self.playing:
            self.log_message("Received /resetbpm but playback is not running.")
            return
        self.user_bpm = max(1, round(self.default_bpm))
        self.smoothed_bpm = float(self.user_bpm)
        self.bpm_slider.set(self.user_bpm)
        self.log_message("BPM reset to default of current .mid file via /resetbpm.")

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
            self.log_message("Skip command issued, but playback is not running.")

    def handle_back(self, address, *args):
        if self.playing:
            self.back_event.set()
            self.log_message("Back requested (OSC).")
        else:
            self.log_message("Back command issued, but playback is not running.")

    def handle_bpm(self, address, *args):
        """
        Called via OSC for /bpm. Smoothing + rounding to int, ignoring if locked or ignoring BPM.
        Then update the slider to keep them in sync.
        """
        if self.bpm_locked or self.ignore_bpm_var.get():
            self.log_message("Got /bpm, but BPM updates are locked or ignored.")
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
            # Ensure the slider matches user_bpm
            self.master.after(0, lambda: self.bpm_slider.set(final_bpm))
            self.log_message(f"/bpm -> {final_bpm}")

    # ----------------- MIDI to OSC ----------------- #
    def run_midi_loop(self, midi_in):
        asyncio.set_event_loop(self.loop)
        self.loop.create_task(self.midi_to_osc(midi_in))

    async def midi_to_osc(self, midi_in):
        while True:
            for message in midi_in.iter_pending():
                await self.process_midi_message(message)
            await asyncio.sleep(0.01)

    async def process_midi_message(self, message):
        """
        Forwards incoming MIDI messages -> OSC (source='input').
        """
        if message.type == 'note_on':
            ch_note = f"/ch{message.channel + 1}note"
            ch_vel = f"/ch{message.channel + 1}nvalue"
            self.osc_client.send_message(ch_note, message.note)
            self.osc_client.send_message(ch_vel, message.velocity)
            self.log_message(f"Input -> {ch_note} {message.note}")
            self.log_message(f"Input -> {ch_vel} {message.velocity}")
        elif message.type == 'note_off':
            ch_note = f"/ch{message.channel + 1}noteoff"
            ch_vel = f"/ch{message.channel + 1}noffvalue"
            self.osc_client.send_message(ch_note, message.note)
            self.osc_client.send_message(ch_vel, 0)
            self.log_message(f"Input -> {ch_note} {message.note}")
            self.log_message(f"Input -> {ch_vel} 0")
        elif message.type == 'control_change':
            osc_address = f"/ch{message.channel + 1}cc{message.control}"
            self.osc_client.send_message(osc_address, message.value)
            self.log_message(f"Input -> {osc_address} {message.value}")
        elif message.type == 'aftertouch':
            osc_address = f"/ch{message.channel + 1}pressure"
            self.osc_client.send_message(osc_address, message.value)
            self.log_message(f"Input -> {osc_address} {message.value}")
        elif message.type == 'pitchwheel':
            osc_address = f"/ch{message.channel + 1}pitch"
            self.osc_client.send_message(osc_address, message.pitch)
            self.log_message(f"Input -> {osc_address} {message.pitch}")

    # ----------------------- Main Execution ------------------------------ #
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
            self.loop.call_soon_threadsafe(self.loop.stop)
            if self.loop_thread and self.loop_thread.is_alive():
                self.loop_thread.join(timeout=1)
            self.master.quit()

    def is_port_in_use(self, port):
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            try:
                s.bind(('0.0.0.0', port))
                return False
            except OSError:
                return True

    async def start_osc_server_async(self, port):
        disp = dispatcher.Dispatcher()
        disp.map("/pause", self.handle_pause)
        disp.map("/play", self.handle_play)
        disp.map("/skip", self.handle_skip)
        disp.map("/back", self.handle_back)
        disp.map("/previous", self.handle_previous)  # Handle /previous OSC message
        disp.map("/bpm", self.handle_bpm)
        disp.map("/bpm1", self.handle_bpm1_toggle)
        disp.map("/resetbpm", self.handle_resetbpm)

        # Map numeric addresses /1, /2, /3 ... /50 for direct playlist selection
        for i in range(1, 51):
            disp.map(f"/{i}", self.handle_numeric_skip)

        server = osc_server.AsyncIOOSCUDPServer(("0.0.0.0", port), disp, self.loop)
        transport, protocol = await server.create_serve_endpoint()
        self.log_message(f"Async OSC Server started on port {port}.")

# ----------------------- Main Execution ------------------------------ #
if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("200x200")  # Start with a small window size
    app = OSCMIDIApp(root)
    root.protocol("WM_DELETE_WINDOW", app.quit_app)  # Ensure proper cleanup on close
    root.mainloop()
