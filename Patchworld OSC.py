import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import logging
import mido
from mido import MidiFile
import threading
import socket
import json
import re
import time
import os
import random
import queue
from datetime import datetime, timedelta
import asyncio
from pythonosc import dispatcher, osc_server, udp_client

# --------------------- Logging Configuration --------------------- #
logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)

# --------------------- Tooltip Class Definition --------------------- #
class Tooltip:
    """Creates a tooltip for a widget when the mouse hovers over it."""
    def __init__(self, widget, text: str = "widget info"):
        self.widget = widget
        self.text = text
        self.tooltip_window = None
        self.widget.bind("<Enter>", self.show_tooltip)
        self.widget.bind("<Leave>", self.hide_tooltip)

    def show_tooltip(self, event=None) -> None:
        if self.tooltip_window or not self.text:
            return
        self.tooltip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        x_offset = self.widget.winfo_rootx() + 20
        y_offset = self.widget.winfo_rooty() + 20
        tw.wm_geometry(f"+{x_offset}+{y_offset}")
        label = tk.Label(
            tw,
            text=self.text,
            justify="left",
            background="#333333",
            foreground="#FFFFFF",
            relief="solid",
            borderwidth=1,
            font=("tahoma", 8, "normal"),
        )
        label.pack(ipadx=1, ipady=1)

    def hide_tooltip(self, event=None) -> None:
        if self.tooltip_window:
            self.tooltip_window.destroy()
        self.tooltip_window = None

# ----------------------- OSCMIDIApp Class ---------------------------- #
class OSCMIDIApp:
    CONFIG_FILE = "config.json"
    MAX_LOG_MESSAGES = 100

    def __init__(self, master: tk.Tk) -> None:
        self.master = master
        self.master.title("OSC2MIDI - Live Edition (Dark)")
        self.setup_theme()

        # Default MIDI channel (1-indexed)
        self.default_midi_channel = 1

        # Playback/Playlist State
        self.original_playlist = []
        self.playlist = []
        self.current_index = 0
        self.playing = False
        self.looping = True
        self.randomize = False

        # Control Events
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

        # MIDI/OSC
        self.midi_out = None
        self.osc_client = None

        # OSC Server
        self.osc_server = None
        self.osc_server_thread = None

        # Alarms
        self.alarms = []

        # UI Visibility Flags
        self.content_visible = False
        self.alarm_frame_visible = False
        self.cc_frame_visible = False

        # Static OSC Addresses (editable)
        self.osc_addresses_in = {
            "pause": "/pause",
            "play": "/play",
            "skip": "/skip",
            "back": "/back",
            "previous": "/previous",
            "bpm": "/bpm",
            "bpm1": "/bpm1",
            "resetbpm": "/resetbpm",
            "generic": "/generic",
        }
        # Only “sync” remains for static outgoing. We removed “aftertouch.”
        self.osc_addresses_out = {
            "sync": "/sync",
        }
        # Dynamic addresses template for incoming:
        self.osc_addresses_in["noteX"] = "/noteX"
        self.osc_addresses_in["noteoffX"] = "/noteoffX"
        self.osc_addresses_in["ccX"] = "/ccX"
        self.osc_addresses_in["pitchX"] = "/pitchX"  # For pitch bend
        self.osc_addresses_in["afterX"] = "/afterX"  # For aftertouch
        self.default_osc_addresses_in = dict(self.osc_addresses_in)
        self.default_osc_addresses_out = dict(self.osc_addresses_out)

        # Note Off Delay default
        self.note_off_delay = 0.5  # seconds

        self.load_icon()
        self.load_config()
        self.setup_ui()
        self.update_clock()
        self.check_alarms()
        self.display_osc_addresses()
        self.master.after(100, self.poll_log_queue)
        self.master.protocol("WM_DELETE_WINDOW", self.quit_app)

    # ---------------- Theming ----------------
    def setup_theme(self) -> None:
        style = ttk.Style(self.master)
        style.theme_use("clam")
        style.configure(".", background="#2B2B2B", foreground="#FFFFFF", bordercolor="#2B2B2B")
        style.configure("TFrame", background="#2B2B2B")
        style.configure("TLabel", background="#2B2B2B", foreground="#FFFFFF")
        style.configure("TButton", background="#3A3A3A", foreground="#FFFFFF")
        style.map("TButton", background=[("active", "#4D4D4D")], foreground=[("active", "#FFFFFF")])
        style.configure("TEntry", foreground="#FFFFFF", background="#3A3A3A",
                        fieldbackground="#3A3A3A", insertcolor="#FFFFFF")
        style.configure("TCombobox", foreground="#FFFFFF", fieldbackground="#3A3A3A", background="#2B2B2B")
        self.master.configure(bg="#2B2B2B")

    # ---------------- Icon, Config, IP ----------------
    def load_icon(self) -> None:
        try:
            icon_path = os.path.join(os.path.dirname(__file__), "icon.png")
            self.master.iconphoto(False, tk.PhotoImage(file=icon_path))
        except Exception as e:
            logging.warning(f"Icon load error: {e}")

    def load_config(self) -> None:
        if os.path.exists(self.CONFIG_FILE):
            with open(self.CONFIG_FILE, "r") as f:
                config = json.load(f)
                self.saved_port = config.get("osc_in_port", "5550")
                self.saved_midi_port = config.get("midi_input_port", "")
                self.saved_midi_out_port = config.get("midi_output_port", "")
                self.saved_out_ip = config.get("osc_out_ip", self.get_local_ip())
                self.saved_out_port = config.get("osc_out_port", "3330")
                # Update addresses from config, if present
                self.osc_addresses_in.update(config.get("osc_addresses_in", {}))
                self.osc_addresses_out.update(config.get("osc_addresses_out", {}))
        else:
            self.saved_port = "5550"
            self.saved_midi_port = ""
            self.saved_midi_out_port = ""
            self.saved_out_ip = self.get_local_ip()
            self.saved_out_port = "3330"

    def save_config(self) -> None:
        config = {
            "osc_in_port": self.saved_port,
            "midi_input_port": self.saved_midi_port,
            "midi_output_port": self.saved_midi_out_port,
            "osc_out_ip": self.saved_out_ip,
            "osc_out_port": self.saved_out_port,
            "osc_addresses_in": self.osc_addresses_in,
            "osc_addresses_out": self.osc_addresses_out,
        }
        with open(self.CONFIG_FILE, "w") as f:
            json.dump(config, f, indent=4)

    def get_local_ip(self) -> str:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        ip = "127.0.0.1"
        try:
            s.connect(("8.8.8.8", 80))
            ip = s.getsockname()[0]
        except Exception:
            pass
        finally:
            s.close()
        return ip

    # ---------------- UI Setup ----------------
    def setup_ui(self) -> None:
        self.master.geometry("500x420")

        # Menu Bar – Static OSC Addresses
        menu_bar = tk.Menu(self.master, bg="#2B2B2B", fg="#FFFFFF")
        self.master.config(menu=menu_bar)
        help_menu = tk.Menu(menu_bar, tearoff=0, bg="#2B2B2B", fg="#FFFFFF")
        menu_bar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="OSC Commands", command=self.show_help)
        addr_menu = tk.Menu(menu_bar, tearoff=0, bg="#2B2B2B", fg="#FFFFFF")
        menu_bar.add_cascade(label="Static OSC Addresses", menu=addr_menu)
        addr_menu.add_command(label="Edit Static OSC Addresses", command=self.open_addresses_editor)

        # Settings Frame
        settings = ttk.Frame(self.master)
        settings.pack(padx=10, pady=10, fill=tk.X)
        ttk.Label(settings, text="IP for OSC In:").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.ip_entry = ttk.Entry(settings)
        self.ip_entry.insert(0, self.get_local_ip())
        self.ip_entry.config(state="readonly")
        self.ip_entry.grid(row=0, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.ip_entry, "Local IP for OSC server.")
        ttk.Label(settings, text="Port for OSC In:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.port_entry = ttk.Entry(settings)
        self.port_entry.insert(0, getattr(self, "saved_port", "5550"))
        self.port_entry.grid(row=1, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.port_entry, "Port where OSC server listens.")
        ttk.Label(settings, text="MIDI Input:").grid(row=2, column=0, sticky=tk.W, pady=2)
        self.midi_input_combo = ttk.Combobox(settings, values=self.get_midi_ports())
        self.midi_input_combo.set(getattr(self, "saved_midi_port", ""))
        self.midi_input_combo.grid(row=2, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.midi_input_combo, "Select MIDI input (optional).")
        ttk.Label(settings, text="MIDI Output:").grid(row=3, column=0, sticky=tk.W, pady=2)
        self.midi_out_combo = ttk.Combobox(settings, values=self.get_midi_output_ports())
        self.midi_out_combo.set(getattr(self, "saved_midi_out_port", ""))
        self.midi_out_combo.grid(row=3, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.midi_out_combo, "Select MIDI output (optional).")
        ttk.Label(settings, text="IP for OSC Out:").grid(row=4, column=0, sticky=tk.W, pady=2)
        self.output_ip_entry = ttk.Entry(settings)
        self.output_ip_entry.insert(0, getattr(self, "saved_out_ip", self.get_local_ip()))
        self.output_ip_entry.grid(row=4, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.output_ip_entry, "Destination IP for OSC messages.")
        ttk.Label(settings, text="Port for OSC Out:").grid(row=5, column=0, sticky=tk.W, pady=2)
        self.output_port_entry = ttk.Entry(settings)
        self.output_port_entry.insert(0, getattr(self, "saved_out_port", "3330"))
        self.output_port_entry.grid(row=5, column=1, sticky=tk.EW, pady=2)
        Tooltip(self.output_port_entry, "Destination port for OSC messages.")
        settings.columnconfigure(1, weight=1)

        # Server Buttons
        server_frame = ttk.Frame(self.master)
        server_frame.pack(pady=5)
        self.bi_dir_button = ttk.Button(server_frame, text="Bi-Directional Server", command=self.start_bi_dir_server)
        self.bi_dir_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.bi_dir_button, "Send & Receive MIDI.")
        self.obs_button = ttk.Button(server_frame, text="OBS Server", command=self.start_obs_server)
        self.obs_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.obs_button, "Only MIDI --> Patch with OBS support.")
        
        # Connection Indicator
        conn_frame = ttk.Frame(self.master)
        conn_frame.pack(pady=5)
        self.connection_indicator = tk.Canvas(conn_frame, width=20, height=20, bg="#2B2B2B", highlightthickness=0)
        self.connection_indicator.pack(side=tk.LEFT, padx=5)
        self.indicator = self.connection_indicator.create_oval(5, 5, 15, 15, fill="red")

        # Note Off Delay UI
        note_off_frame = ttk.Frame(self.master)
        note_off_frame.pack(fill=tk.X, padx=10, pady=5)

        ttk.Label(note_off_frame, text="Note Off Delay:").pack(side=tk.LEFT, padx=5)
        self.note_off_delay_slider = tk.Scale(
            note_off_frame, from_=0.0, to=5.0, resolution=0.01,
            orient=tk.HORIZONTAL, length=120, command=self.update_note_off_delay,
            bg="#2B2B2B", fg="#FFFFFF", troughcolor="#3A3A3A", activebackground="#4D4D4D"
        )
        self.note_off_delay_slider.set(self.note_off_delay)
        self.note_off_delay_slider.pack(side=tk.LEFT, padx=5)
        Tooltip(self.note_off_delay_slider, "Time (secs) before auto note_off is sent after a /noteX message.")

        ttk.Label(note_off_frame, text="OSC Address:").pack(side=tk.LEFT, padx=5)
        self.note_off_delay_address_entry = ttk.Entry(note_off_frame, width=10)
        # Changed default to "/delay"
        self.note_off_delay_address_entry.insert(0, "/delay")
        self.note_off_delay_address_entry.pack(side=tk.LEFT, padx=5)
        Tooltip(self.note_off_delay_address_entry, "OSC address that sets this delay slider value.")

        # Burger Menus
        burger = ttk.Frame(self.master)
        burger.pack(pady=2)
        self.menu_button = ttk.Button(burger, text="≡ Midi Player/Log", command=self.toggle_midi_menu, width=17)
        self.menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.menu_button, "Toggle MIDI Player/Log UI.")
        self.alarm_menu_button = ttk.Button(burger, text="≡ Alarm Clock", command=self.toggle_alarm_menu, width=17)
        self.alarm_menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.alarm_menu_button, "Toggle Alarm Clock UI.")
        self.cc_menu_button = ttk.Button(burger, text="≡ CC", command=self.toggle_cc_menu, width=17)
        self.cc_menu_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.cc_menu_button, "Toggle CC controls UI.")

        # Content Frames
        self.content_frame = ttk.Frame(self.master)
        self.setup_midi_ui()
        self.alarm_frame = ttk.Frame(self.master)
        self.setup_alarm_ui()
        self.cc_frame = ttk.Frame(self.master)
        self.setup_cc_ui()
        self.load_bottom_logo()

    def update_note_off_delay(self, val_str):
        """Callback for the note_off delay slider (UI)."""
        try:
            val = float(val_str)
            if val < 0:
                val = 0
            elif val > 5:
                val = 5
            self.note_off_delay = val
            self.log_message(f"Note Off Delay set to {val} sec (via slider)")
        except ValueError:
            pass

    def load_bottom_logo(self) -> None:
        try:
            path = os.path.join(os.path.dirname(__file__), "bottomlogo.png")
            orig = tk.PhotoImage(file=path)
            self.bottom_logo = orig.subsample(2, 2)
            lbl = tk.Label(self.master, image=self.bottom_logo, bg="#2B2B2B")
            lbl.pack(side=tk.BOTTOM, pady=5)
        except Exception as e:
            logging.debug(f"Bottom logo load error: {e}")

    def get_midi_ports(self):
        try:
            return mido.get_input_names()
        except Exception:
            return []

    def get_midi_output_ports(self):
        try:
            return mido.get_output_names()
        except Exception:
            return []

    # ---------------- MIDI/Log Frame ----------------
    def setup_midi_ui(self) -> None:
        ctrl_frame = ttk.Frame(self.content_frame)
        ctrl_frame.pack(pady=5)
        self.play_button = ttk.Button(ctrl_frame, text="Play", command=self.play)
        self.play_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.play_button, "Start playback.")
        self.stop_button = ttk.Button(ctrl_frame, text="Stop", command=self.stop)
        self.stop_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.stop_button, "Stop playback.")
        self.skip_button = ttk.Button(ctrl_frame, text="Skip", command=self.skip)
        self.skip_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.skip_button, "Skip to next track.")
        self.back_button = ttk.Button(ctrl_frame, text="Back", command=self.back)
        self.back_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.back_button, "Restart current track.")
        self.previous_button = ttk.Button(ctrl_frame, text="Previous", command=self.previous)
        self.previous_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.previous_button, "Previous track.")

        file_frame = ttk.Frame(self.content_frame)
        file_frame.pack(pady=5)
        self.load_button = ttk.Button(file_frame, text="Load MIDI", command=self.load_file)
        self.load_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.load_button, "Load a MIDI file.")
        self.load_folder_button = ttk.Button(file_frame, text="Load Folder", command=self.load_folder)
        self.load_folder_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.load_folder_button, "Load MIDI files from folder.")
        self.unload_button = ttk.Button(file_frame, text="Unload Playlist", command=self.unload_playlist)
        self.unload_button.pack(side=tk.LEFT, padx=5)
        Tooltip(self.unload_button, "Clear playlist.")

        playb_frame = ttk.Frame(self.content_frame)
        playb_frame.pack(pady=5)
        self.looping_var = tk.BooleanVar(value=self.looping)
        self.looping_checkbutton = ttk.Checkbutton(playb_frame, text="Loop Playlist", variable=self.looping_var, command=self.toggle_looping)
        self.looping_checkbutton.pack(side=tk.LEFT, padx=5)
        self.randomize_button = ttk.Button(playb_frame, text="Randomize Playlist", command=self.toggle_randomize_playlist)
        self.randomize_button.pack(side=tk.LEFT, padx=5)
        self.sync_checkbutton = ttk.Checkbutton(playb_frame, text="Sync BPM", variable=self.sync_var, command=self.toggle_sync)
        self.sync_checkbutton.pack(side=tk.LEFT, padx=5)
        self.info_label = tk.Label(self.content_frame, text="No file loaded", fg="#FFFFFF", bg="#2B2B2B")
        self.info_label.pack(pady=5)

        bpm_frame = ttk.Frame(self.content_frame)
        bpm_frame.pack(pady=5, fill=tk.X)
        ttk.Label(bpm_frame, text="Tempo (BPM):").pack(side=tk.LEFT)
        self.bpm_slider = tk.Scale(bpm_frame, from_=20, to=420, orient=tk.HORIZONTAL, command=self.update_bpm,
                                   bg="#2B2B2B", fg="#FFFFFF", troughcolor="#3A3A3A", activebackground="#4D4D4D")
        self.bpm_slider.set(self.user_bpm)
        self.bpm_slider.pack(side=tk.LEFT, padx=5)
        self.reset_bpm_button = ttk.Button(bpm_frame, text="Reset Tempo", command=self.reset_bpm)
        self.reset_bpm_button.pack(side=tk.LEFT, padx=5)
        self.lock_bpm_button = ttk.Button(bpm_frame, text="Lock Tempo", command=self.toggle_lock_bpm)
        self.lock_bpm_button.pack(side=tk.LEFT, padx=5)
        self.ignore_bpm_checkbox = ttk.Checkbutton(bpm_frame, text="Ignore /bpm", variable=self.ignore_bpm_var, command=self.toggle_ignore_bpm)
        self.ignore_bpm_checkbox.pack(side=tk.LEFT, padx=5)

        log_frame = ttk.Frame(self.content_frame)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10)
        tk.Label(self.content_frame, text="Log Messages:", bg="#2B2B2B", fg="#FFFFFF").pack()
        self.log_text = tk.Text(log_frame, height=8, width=70, state="disabled", bg="#1E1E1E", fg="#FFFFFF", wrap="word")
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        log_scroll = ttk.Scrollbar(log_frame, command=self.log_text.yview)
        self.log_text.config(yscrollcommand=log_scroll.set)
        log_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        playlist_frame = ttk.Frame(self.content_frame)
        playlist_frame.pack(fill=tk.BOTH, expand=True, padx=10)
        tk.Label(self.content_frame, text="Playlist:", bg="#2B2B2B", fg="#FFFFFF").pack()
        self.playlist_box = tk.Listbox(playlist_frame, selectmode=tk.SINGLE,
                                       bg="#1E1E1E", fg="#FFFFFF", selectbackground="#3A3A3A", height=10)
        self.playlist_box.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        play_scroll = ttk.Scrollbar(playlist_frame, command=self.playlist_box.yview)
        self.playlist_box.config(yscrollcommand=play_scroll.set)
        play_scroll.pack(side=tk.RIGHT, fill=tk.Y)

    # ---------------- Alarm Clock UI ----------------
    def setup_alarm_ui(self) -> None:
        # Header with centered current date/time
        header = tk.Label(self.alarm_frame, text="", font=("Helvetica", 14, "bold"), bg="#2B2B2B", fg="#FFFFFF")
        header.pack(fill=tk.X, pady=5)
        self.clock_label = header  # update_clock will update this label

        # Alarm controls arranged neatly
        controls = ttk.Frame(self.alarm_frame)
        controls.pack(pady=5)
        ttk.Label(controls, text="Date (YYYY-MM-DD):").grid(row=0, column=0, padx=5, pady=5, sticky=tk.E)
        self.alarm_date_entry = ttk.Entry(controls, width=12)
        self.alarm_date_entry.grid(row=0, column=1, padx=5, pady=5, sticky=tk.W)
        ttk.Label(controls, text="Time (HH:MM:SS):").grid(row=1, column=0, padx=5, pady=5, sticky=tk.E)
        self.alarm_time_entry = ttk.Entry(controls, width=10)
        self.alarm_time_entry.grid(row=1, column=1, padx=5, pady=5, sticky=tk.W)
        ttk.Label(controls, text="OSC Address:").grid(row=2, column=0, padx=5, pady=5, sticky=tk.E)
        self.alarm_address_entry = ttk.Entry(controls, width=20)
        self.alarm_address_entry.grid(row=2, column=1, padx=5, pady=5, sticky=tk.W)
        ttk.Label(controls, text="OSC Args (comma separated):").grid(row=3, column=0, padx=5, pady=5, sticky=tk.E)
        self.alarm_args_entry = ttk.Entry(controls, width=20)
        self.alarm_args_entry.grid(row=3, column=1, padx=5, pady=5, sticky=tk.W)
        self.schedule_alarm_button = ttk.Button(controls, text="Schedule Alarm", command=self.schedule_alarm)
        self.schedule_alarm_button.grid(row=4, column=0, columnspan=2, pady=5)

        # Set default values for alarm inputs:
        now = datetime.now()
        self.alarm_date_entry.insert(0, now.strftime("%Y-%m-%d"))
        self.alarm_time_entry.insert(0, (now + timedelta(minutes=2)).strftime("%H:%M:%S"))
        self.alarm_address_entry.insert(0, "/alarm")
        self.alarm_args_entry.insert(0, "1")

        # Alarm list label using tk.Label
        tk.Label(self.alarm_frame, text="Scheduled Alarms:", bg="#2B2B2B", fg="#FFFFFF").pack(pady=5)
        list_frame = ttk.Frame(self.alarm_frame)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10)
        self.alarm_listbox = tk.Listbox(list_frame, selectmode=tk.SINGLE,
                                        bg="#1E1E1E", fg="#FFFFFF", selectbackground="#3A3A3A", height=8)
        self.alarm_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        al_scroll = ttk.Scrollbar(list_frame, command=self.alarm_listbox.yview)
        self.alarm_listbox.config(yscrollcommand=al_scroll.set)
        al_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.remove_alarm_button = ttk.Button(self.alarm_frame, text="Remove Selected Alarm", command=self.remove_selected_alarm)
        self.remove_alarm_button.pack(pady=5)

    # ---------------- CC Controls ----------------
    def setup_cc_ui(self) -> None:
        self.cc_sliders = []
        self.cc_address_entries = []
        ttk.Label(self.cc_frame, text="CC Controls", foreground="#FFFFFF").pack(pady=5)
        cc_frame = ttk.Frame(self.cc_frame)
        cc_frame.pack(padx=10, pady=10, fill=tk.X)
        for i in range(6):
            row = ttk.Frame(cc_frame)
            row.pack(fill=tk.X, pady=3)
            ttk.Label(row, text=f"CC {i+1}:", width=10).pack(side=tk.LEFT, padx=5)
            slider = tk.Scale(row, from_=0, to=127, orient=tk.HORIZONTAL, length=150,
                              bg="#2B2B2B", fg="#FFFFFF", troughcolor="#3A3A3A", activebackground="#4D4D4D",
                              command=lambda val, idx=i: self.send_cc_message(idx))
            slider.set(0)
            slider.pack(side=tk.LEFT, padx=5)
            self.cc_sliders.append(slider)
            entry = ttk.Entry(row, width=15)
            entry.insert(0, f"/cc{i+1}")
            entry.pack(side=tk.LEFT, padx=5)
            self.cc_address_entries.append(entry)

    # ---------------- Log Handling ----------------
    def log_message(self, message: str, level: int = logging.INFO) -> None:
        logging.log(level, message)
        if len(self.log_messages) >= self.MAX_LOG_MESSAGES:
            self.log_messages.pop(0)
        self.log_messages.append(message)
        self.log_queue.put(message)

    def poll_log_queue(self) -> None:
        while not self.log_queue.empty():
            msg = self.log_queue.get()
            self.log_text.config(state="normal")
            self.log_text.insert(tk.END, f"{msg}\n")
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

    # ---------------- Playlist Management ----------------
    def load_file(self) -> None:
        path = filedialog.askopenfilename(filetypes=[("MIDI Files", "*.mid *.midi")])
        if path:
            self.playlist.append(path)
            self.original_playlist.append(path)
            self.playlist_box.insert(tk.END, f"{len(self.playlist)}: {os.path.basename(path)}")
            self.info_label.config(text=f"Loaded: {path}")
            self.log_message(f"Loaded MIDI file: {path}")
        else:
            self.info_label.config(text="No file selected.")
            self.log_message("No file selected.")

    def load_folder(self) -> None:
        folder = filedialog.askdirectory()
        if folder:
            files = [os.path.join(folder, f) for f in os.listdir(folder) if f.lower().endswith(('.mid', '.midi'))]
            if files:
                for f in files:
                    self.playlist.append(f)
                    self.original_playlist.append(f)
                    self.playlist_box.insert(tk.END, f"{len(self.playlist)}: {os.path.basename(f)}")
                self.info_label.config(text=f"Loaded {len(files)} MIDI files.")
                self.log_message(f"Loaded {len(files)} files from {folder}")
            else:
                messagebox.showinfo("No MIDI Files", "No MIDI files found.")
                self.log_message("No MIDI files found in folder.")
        else:
            self.info_label.config(text="No folder selected.")
            self.log_message("No folder selected.")

    def unload_playlist(self) -> None:
        if self.playing:
            messagebox.showwarning("Stop Playback", "Stop playback before unloading playlist.")
            return
        self.playlist.clear()
        self.original_playlist.clear()
        self.playlist_box.delete(0, tk.END)
        self.info_label.config(text="Playlist unloaded.")
        self.log_message("Playlist unloaded.")

    def update_playlist_box(self) -> None:
        self.playlist_box.delete(0, tk.END)
        for i, f in enumerate(self.playlist, start=1):
            self.playlist_box.insert(tk.END, f"{i}: {os.path.basename(f)}")

    # ---------------- Playback Controls ----------------
    def play(self) -> None:
        if not self.playlist:
            self.info_label.config(text="No MIDI files loaded.")
            self.log_message("No MIDI files to play.")
            return
        if not self.playing:
            self.playing = True
            self.current_index = 0
            self.log_message("Playback started.")
            threading.Thread(target=self._play_midi_playlist, daemon=True).start()
        else:
            self.log_message("Playback already running.")

    def stop(self) -> None:
        if self.playing:
            self.playing = False
            self.pause_event.clear()
            self.skip_event.set()
            self.back_event.set()
            self.previous_event.set()
            self.skip_to_event.set()
            self.info_label.config(text="Playback stopped.")
            self.log_message("Playback stopped.")
        else:
            self.log_message("Stop requested, but nothing is playing.")

    def skip(self) -> None:
        if self.playing:
            self.skip_event.set()
            self.log_message("Skip requested.")
        else:
            self.log_message("Skip requested, but no playback active.")

    def back(self) -> None:
        if self.playing:
            self.back_event.set()
            self.log_message("Restart requested.")
        else:
            self.log_message("Back requested, but nothing is playing.")

    def previous(self) -> None:
        if self.playing:
            if self.current_index > 0:
                self.previous_event.set()
                self.log_message("Previous track requested.")
            else:
                self.log_message("Already at first track.")
        else:
            self.log_message("Previous requested, but nothing is playing.")

    def skip_to_number(self, num: int) -> None:
        if not self.playing:
            self.log_message(f"Skip to {num} requested but no playback active.")
            return
        if 1 <= num <= len(self.playlist):
            self.skip_to_index = num - 1
            self.skip_to_event.set()
            self.log_message(f"Skip to track #{num}.")
        else:
            self.log_message(f"Invalid track number: {num}.")

    def toggle_looping(self) -> None:
        self.looping = self.looping_var.get()
        self.log_message(f"Looping {'enabled' if self.looping else 'disabled'}.")

    def toggle_randomize_playlist(self) -> None:
        self.randomize = not self.randomize
        if self.randomize:
            if len(self.playlist) > 1:
                random.shuffle(self.playlist)
                self.update_playlist_box()
                self.current_index = 0
                self.log_message("Playlist randomized.")
            else:
                self.log_message("Not enough files to randomize.")
        else:
            self.playlist = self.original_playlist.copy()
            self.update_playlist_box()
            self.current_index = 0
            self.log_message("Playlist restored to original order.")
        self.randomize_button.config(text="Restore Order" if self.randomize else "Randomize Playlist")

    def _play_midi_playlist(self) -> None:
        try:
            while self.playing and (0 <= self.current_index < len(self.playlist)):
                f = self.playlist[self.current_index]
                self._play_single_midi(f)
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
                    if self.skip_to_index is not None and 0 <= self.skip_to_index < len(self.playlist):
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
        except Exception as e:
            self.playing = False
            self.log_message(f"Playback error: {e}", level=logging.ERROR)
            self.info_label.config(text=f"Playback Error: {e}")

    def _play_single_midi(self, path: str) -> None:
        self.info_label.config(text=f"Playing: {path}")
        self.log_message(f"Playing {path}")
        try:
            mid = MidiFile(path)
        except Exception as e:
            self.log_message(f"Failed to load MIDI: {e}", level=logging.ERROR)
            return
        if not self.bpm_locked:
            bpm = self.get_file_bpm(mid)
            if bpm:
                self.default_bpm = max(1, round(bpm))
                self.smoothed_bpm = float(self.default_bpm)
                self.user_bpm = self.default_bpm
                self.master.after(0, lambda: self.bpm_slider.set(self.user_bpm))
                self.log_message(f"Default BPM set to {self.default_bpm}")
            else:
                self.log_message("No BPM found; using previous BPM.")
        self.ticks_per_beat = mid.ticks_per_beat
        events = []
        for track in mid.tracks:
            abs_ticks = 0
            for msg in track:
                abs_ticks += msg.time
                if not msg.is_meta:
                    events.append((abs_ticks, msg))
        events.sort(key=lambda x: x[0])
        last_ticks = 0
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
            delta = abs_ticks - last_ticks
            last_ticks = abs_ticks
            if delta > 0:
                t_delay = (delta / self.ticks_per_beat) * (60.0 / self.default_bpm) * (self.default_bpm / self.user_bpm)
                time.sleep(t_delay)
            self.handle_midi_message(msg, source="playback")

    def get_file_bpm(self, mid: MidiFile):
        for track in mid.tracks:
            for msg in track:
                if msg.type == "set_tempo":
                    return mido.tempo2bpm(msg.tempo)
        return None

    # ---------------- MIDI Message Handling ----------------
    def handle_midi_message(self, msg, source="input") -> None:
        """Handles MIDI -> OSC (outgoing)"""
        if hasattr(msg, "channel"):
            ch = msg.channel + 1
            if msg.type == "note_on":
                if msg.velocity > 0:
                    if self.osc_client:
                        addr = f"/note{ch}"
                        self.osc_client.send_message(addr, [msg.note, msg.velocity])
                        self.log_message(f"Sent OSC -> {addr} [{msg.note}, {msg.velocity}]")
                else:
                    if self.osc_client:
                        addr = f"/noteoff{ch}"
                        self.osc_client.send_message(addr, [msg.note, 0])
                        self.log_message(f"Sent OSC -> {addr} [{msg.note}, 0]")
            elif msg.type == "note_off":
                if self.osc_client:
                    addr = f"/noteoff{ch}"
                    self.osc_client.send_message(addr, [msg.note, 0])
                    self.log_message(f"Sent OSC -> {addr} [{msg.note}, 0]")
            elif msg.type == "control_change":
                if self.osc_client:
                    addr = f"/cc{ch}"
                    self.osc_client.send_message(addr, [msg.control, msg.value])
                    self.log_message(f"Sent OSC -> {addr} [{msg.control}, {msg.value}]")
            elif msg.type == "pitchwheel":
                if self.osc_client:
                    addr = f"/pitch{ch}"
                    self.osc_client.send_message(addr, [msg.pitch])
                    self.log_message(f"Sent OSC -> {addr} [{msg.pitch}]")
            elif msg.type == "aftertouch":
                if self.osc_client:
                    # Now dynamic /afterX for aftertouch
                    addr = f"/after{ch}"
                    self.osc_client.send_message(addr, [msg.value])
                    self.log_message(f"Sent OSC -> {addr} [{msg.value}]")
            else:
                self.log_message(f"Ignored MIDI message: {msg.type}", level=logging.DEBUG)
        else:
            self.log_message(f"Ignored MIDI message without channel: {msg}", level=logging.DEBUG)

    # ---------------- Dynamic OSC Handlers (Incoming) ----------------
    def handle_osc_note_dynamic(self, address, *args):
        m = re.match(r'/note(\d+)$', address)
        if not m:
            self.log_message(f"Invalid dynamic note address: {address}", level=logging.ERROR)
            return
        try:
            ch = int(m.group(1))
        except Exception as e:
            self.log_message(f"Error parsing dynamic note channel: {e}", level=logging.ERROR)
            return
        if len(args) < 2:
            self.log_message("Dynamic /note received with insufficient args.", level=logging.ERROR)
            return
        try:
            note = int(args[0])
            raw_vel = float(args[1])
        except Exception as e:
            self.log_message(f"Error parsing dynamic /note args: {e}", level=logging.ERROR)
            return

        # Convert 0–1 to 0–127, clamp
        if raw_vel <= 1.0:
            vel = int(max(0, min(127, raw_vel * 127)))
        else:
            vel = int(max(0, min(127, raw_vel)))  # clamp

        msg = mido.Message("note_on", channel=ch-1, note=note, velocity=vel)
        if self.midi_out:
            try:
                self.midi_out.send(msg)
                self.log_message(f"OSC->MIDI: note_on (chan {ch}) note={note}, velocity={vel}")
            except Exception as e:
                self.log_message(f"MIDI Output error in dynamic /note: {e}", level=logging.ERROR)
        else:
            self.log_message("MIDI Output not set for dynamic /note.", level=logging.ERROR)

        # Use the user-defined slider delay:
        delay = self.note_off_delay
        threading.Timer(delay, self.send_note_off_dynamic, args=(note, ch)).start()

    def send_note_off_dynamic(self, note, ch):
        if not self.midi_out:
            self.log_message("MIDI Output not set for dynamic note_off.", level=logging.ERROR)
            return
        msg = mido.Message("note_off", channel=ch-1, note=note, velocity=0)
        try:
            self.midi_out.send(msg)
            self.log_message(f"OSC->MIDI: note_off (chan {ch}) note={note}, velocity=0")
        except Exception as e:
            self.log_message(f"MIDI Output error in dynamic note_off: {e}", level=logging.ERROR)

    def handle_osc_noteoff_dynamic(self, address, *args):
        m = re.match(r'/noteoff(\d+)$', address)
        if not m:
            self.log_message(f"Invalid dynamic noteoff address: {address}", level=logging.ERROR)
            return
        try:
            ch = int(m.group(1))
        except Exception as e:
            self.log_message(f"Error parsing dynamic noteoff channel: {e}", level=logging.ERROR)
            return
        if len(args) < 2:
            self.log_message("Dynamic /noteoff received with insufficient args.", level=logging.ERROR)
            return
        try:
            note = int(args[0])
        except Exception as e:
            self.log_message(f"Error parsing dynamic /noteoff args: {e}", level=logging.ERROR)
            return
        msg = mido.Message("note_off", channel=ch-1, note=note, velocity=0)
        if self.midi_out:
            try:
                self.midi_out.send(msg)
                self.log_message(f"OSC->MIDI: note_off (chan {ch}) note={note}, velocity=0")
            except Exception as e:
                self.log_message(f"MIDI Output error in dynamic noteoff: {e}", level=logging.ERROR)
        else:
            self.log_message("MIDI Output not set for dynamic noteoff.", level=logging.ERROR)

    def handle_osc_cc_dynamic(self, address, *args):
        m = re.match(r'/cc(\d+)$', address)
        if not m:
            self.log_message(f"Invalid dynamic cc address: {address}", level=logging.ERROR)
            return
        try:
            ch = int(m.group(1))
        except Exception as e:
            self.log_message(f"Error parsing dynamic cc channel: {e}", level=logging.ERROR)
            return
        if len(args) < 2:
            self.log_message("Dynamic /cc received with insufficient args.", level=logging.ERROR)
            return
        try:
            cc_num = int(args[0])
            raw_val = float(args[1])
            if raw_val <= 1.0:
                cc_val = int(max(0, min(127, raw_val * 127)))
            else:
                cc_val = int(max(0, min(127, raw_val)))
        except Exception as e:
            self.log_message(f"Error parsing dynamic /cc args: {e}", level=logging.ERROR)
            return
        msg = mido.Message("control_change", channel=ch-1, control=cc_num, value=cc_val)
        if self.midi_out:
            try:
                self.midi_out.send(msg)
                self.log_message(f"OSC->MIDI: cc (chan {ch}) cc={cc_num}, value={cc_val}")
            except Exception as e:
                self.log_message(f"MIDI Output error in dynamic cc: {e}", level=logging.ERROR)
        else:
            self.log_message("MIDI Output not set for dynamic cc.", level=logging.ERROR)

    def handle_osc_pitch_dynamic(self, address, *args):
        m = re.match(r'/pitch(\d+)$', address)
        if not m:
            self.log_message(f"Invalid dynamic pitch address: {address}", level=logging.ERROR)
            return
        try:
            ch = int(m.group(1))
        except Exception as e:
            self.log_message(f"Error parsing dynamic pitch channel: {e}", level=logging.ERROR)
            return
        if len(args) < 1:
            self.log_message("Dynamic /pitch received with insufficient args.", level=logging.ERROR)
            return
        try:
            pitch = int(args[0])
        except Exception as e:
            self.log_message(f"Error parsing dynamic /pitch args: {e}", level=logging.ERROR)
            return
        msg = mido.Message("pitchwheel", channel=ch-1, pitch=pitch)
        if self.midi_out:
            try:
                self.midi_out.send(msg)
                self.log_message(f"OSC->MIDI: pitchwheel (chan {ch}) pitch={pitch}")
            except Exception as e:
                self.log_message(f"MIDI Output error in dynamic pitch: {e}", level=logging.ERROR)
        else:
            self.log_message("MIDI Output not set for dynamic pitch.", level=logging.ERROR)

    def handle_osc_after_dynamic(self, address, *args):
        m = re.match(r'/after(\d+)$', address)
        if not m:
            self.log_message(f"Invalid dynamic aftertouch address: {address}", level=logging.ERROR)
            return
        try:
            ch = int(m.group(1))
        except Exception as e:
            self.log_message(f"Error parsing dynamic aftertouch channel: {e}", level=logging.ERROR)
            return
        if len(args) < 1:
            self.log_message("Dynamic /after received with insufficient args.", level=logging.ERROR)
            return
        try:
            val = int(float(args[0]))
        except Exception as e:
            self.log_message(f"Error parsing dynamic /after args: {e}", level=logging.ERROR)
            return
        msg = mido.Message("aftertouch", channel=ch-1, value=val)
        if self.midi_out:
            try:
                self.midi_out.send(msg)
                self.log_message(f"OSC->MIDI: aftertouch (chan {ch}) value={val}")
            except Exception as e:
                self.log_message(f"MIDI Output error in dynamic aftertouch: {e}", level=logging.ERROR)
        else:
            self.log_message("MIDI Output not set for dynamic aftertouch.", level=logging.ERROR)

    def handle_osc_generic(self, address, *args):
        if len(args) < 1:
            self.log_message("Generic OSC received with insufficient args.", level=logging.ERROR)
            return
        try:
            midi_type = str(args[0]).lower()
            params = list(args[1:])
        except Exception as e:
            self.log_message(f"Error parsing generic OSC args: {e}", level=logging.ERROR)
            return

        # Default expectations: note_on/note_off expect 2 parameters, etc.
        expected = {"note_on": 2, "note_off": 2, "control_change": 2, "pitchwheel": 1, "aftertouch": 1}
        exp = expected.get(midi_type, None)
        if exp is not None:
            if len(params) < exp:
                params.extend([0] * (exp - len(params)))
        extra = params[exp:] if (exp is not None and len(params) > exp) else []
        try:
            kwargs = {"channel": self.default_midi_channel - 1}
            if midi_type in ["note_on", "note_off"]:
                if len(params) < 2:
                    raise ValueError("Not enough parameters for note message.")
                kwargs["note"] = int(params[0])
                raw_vel = float(params[1])
                # clamp velocity
                vel = int(max(0, min(127, raw_vel*127))) if raw_vel <= 1 else int(max(0, min(127, raw_vel)))
                kwargs["velocity"] = vel
            elif midi_type == "control_change":
                if len(params) < 2:
                    raise ValueError("Not enough parameters for control_change.")
                kwargs["control"] = int(params[0])
                raw_val = float(params[1])
                cc_val = int(max(0, min(127, raw_val*127))) if raw_val <= 1 else int(max(0, min(127, raw_val)))
                kwargs["value"] = cc_val
            elif midi_type == "pitchwheel":
                if len(params) < 1:
                    raise ValueError("Not enough parameters for pitchwheel.")
                kwargs["pitch"] = int(params[0])
            elif midi_type == "aftertouch":
                if len(params) < 1:
                    raise ValueError("Not enough parameters for aftertouch.")
                kwargs["value"] = int(params[0])
            else:
                kwargs["data"] = params
            if extra:
                kwargs["data"] = extra
            msg = mido.Message(midi_type, **kwargs)
        except Exception as e:
            self.log_message(f"Error building generic MIDI message: {e}", level=logging.ERROR)
            return
        if self.midi_out:
            try:
                self.midi_out.send(msg)
                self.log_message(f"Generic OSC -> Sent MIDI: {msg}")
            except Exception as e:
                self.log_message(f"MIDI Output error in generic OSC: {e}", level=logging.ERROR)
        else:
            self.log_message("MIDI Output not set; generic OSC ignored.", level=logging.ERROR)

    # ---------------- Alarm Clock ----------------
    def update_clock(self) -> None:
        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.clock_label.config(text=now_str)
        self.master.after(1000, self.update_clock)

    def check_alarms(self) -> None:
        now = datetime.now()
        for alarm in self.alarms:
            if not alarm["triggered"] and now >= alarm["datetime"]:
                addr = alarm["address"]
                args = alarm["args"]
                self.log_message(f"Alarm triggered -> sending OSC to {addr} with args {args}")
                if self.osc_client:
                    if args:
                        parsed = []
                        for a in args:
                            try:
                                parsed.append(int(a))
                            except ValueError:
                                try:
                                    parsed.append(float(a))
                                except ValueError:
                                    parsed.append(a)
                        self.osc_client.send_message(addr, parsed)
                    else:
                        self.osc_client.send_message(addr, [])
                alarm["triggered"] = True
        self.master.after(1000, self.check_alarms)

    def schedule_alarm(self) -> None:
        d_str = self.alarm_date_entry.get().strip()
        t_str = self.alarm_time_entry.get().strip()
        addr = self.alarm_address_entry.get().strip()
        arg_str = self.alarm_args_entry.get().strip()
        if not d_str or not t_str or not addr:
            messagebox.showwarning("Incomplete Data", "Enter Date, Time, and OSC Address.")
            return
        try:
            dt = datetime.strptime(f"{d_str} {t_str}", "%Y-%m-%d %H:%M:%S")
            if dt <= datetime.now():
                messagebox.showwarning("Invalid Time", "Alarm time must be in the future.")
                return
        except ValueError:
            messagebox.showwarning("Invalid Date/Time", "Use YYYY-MM-DD and HH:MM:SS (24-hour).")
            return
        # Split the argument string on commas and trim whitespace
        args = [a.strip() for a in arg_str.split(",")] if arg_str else []
        alarm = {"datetime": dt, "address": addr, "args": args, "triggered": False}
        self.alarms.append(alarm)
        self.alarm_listbox.insert(tk.END, f"{dt.strftime('%Y-%m-%d %H:%M:%S')} -> {addr} {' '.join(args)}")
        self.log_message(f"Scheduled alarm at {dt} for {addr} with args {args}")
        # Reset the fields to defaults.
        now = datetime.now()
        self.alarm_date_entry.delete(0, tk.END)
        self.alarm_date_entry.insert(0, now.strftime("%Y-%m-%d"))
        self.alarm_time_entry.delete(0, tk.END)
        self.alarm_time_entry.insert(0, (now + timedelta(minutes=2)).strftime("%H:%M:%S"))
        self.alarm_address_entry.delete(0, tk.END)
        self.alarm_address_entry.insert(0, "/alarm")
        self.alarm_args_entry.delete(0, tk.END)
        self.alarm_args_entry.insert(0, "1")

    def remove_selected_alarm(self) -> None:
        sel = self.alarm_listbox.curselection()
        if not sel:
            messagebox.showwarning("No Selection", "Select an alarm to remove.")
            return
        idx = sel[0]
        self.alarm_listbox.delete(idx)
        rem = self.alarms.pop(idx)
        self.log_message(f"Removed alarm: {rem}")

    # ---------------- OBS and Bi-Directional Server Functions ----------------
    def start_bi_dir_server(self) -> None:
        if self.bi_dir_button["text"] == "Bi-Directional Server":
            midi_in_name = self.midi_input_combo.get()
            midi_out_name = self.midi_out_combo.get()
            osc_out_ip = self.output_ip_entry.get()
            try:
                osc_out_port = int(self.output_port_entry.get())
                osc_in_port = int(self.port_entry.get())
            except ValueError:
                messagebox.showerror("Error", "Invalid port number.")
                return
            if self.is_port_in_use(osc_in_port):
                messagebox.showerror("Error", f"Port {osc_in_port} is in use.")
                return
            if midi_in_name:
                try:
                    midi_in = mido.open_input(midi_in_name)
                    threading.Thread(target=self.run_midi_loop, args=(midi_in,), daemon=True).start()
                except Exception as e:
                    messagebox.showwarning("MIDI Input Error", f"Cannot open MIDI input: {e}")
            if midi_out_name:
                try:
                    self.midi_out = mido.open_output(midi_out_name)
                except Exception as e:
                    messagebox.showwarning("MIDI Output Error", f"Cannot open MIDI output: {e}")
            self.osc_client = udp_client.SimpleUDPClient(osc_out_ip, osc_out_port)
            self.saved_out_ip = osc_out_ip
            self.saved_out_port = osc_out_port
            self.saved_port = osc_in_port
            self.saved_midi_port = midi_in_name
            self.saved_midi_out_port = midi_out_name
            self.save_config()
            self.osc_server_thread = threading.Thread(target=self.start_osc_server_thread, args=(osc_in_port,), daemon=True)
            self.osc_server_thread.start()
            self.bi_dir_button.config(text="Stop and Close")
            self.obs_button.config(text="Stop and Close")
            self.log_message("Bi-Directional OSC Server started (threaded).")
            self.set_connection_status("green")
        else:
            self.quit_app()

    def start_obs_server(self) -> None:
        if self.obs_button["text"] == "OBS Server":
            midi_in_name = self.midi_input_combo.get()
            midi_out_name = self.midi_out_combo.get()
            osc_out_ip = self.output_ip_entry.get()
            try:
                osc_out_port = int(self.output_port_entry.get())
                osc_in_port = int(self.port_entry.get())
            except ValueError:
                messagebox.showerror("Error", "Invalid port number.")
                return
            if self.is_port_in_use(osc_in_port):
                messagebox.showerror("Error", f"Port {osc_in_port} is in use.")
                return
            if midi_in_name:
                try:
                    midi_in = mido.open_input(midi_in_name)
                    threading.Thread(target=self.run_midi_loop, args=(midi_in,), daemon=True).start()
                except Exception as e:
                    messagebox.showwarning("MIDI Input Error", f"Cannot open MIDI input: {e}")
            if midi_out_name:
                try:
                    self.midi_out = mido.open_output(midi_out_name)
                except Exception as e:
                    messagebox.showwarning("MIDI Output Error", f"Cannot open MIDI output: {e}")
            self.osc_client = udp_client.SimpleUDPClient(osc_out_ip, osc_out_port)
            self.saved_out_ip = osc_out_ip
            self.saved_out_port = osc_out_port
            self.saved_port = osc_in_port
            self.saved_midi_port = midi_in_name
            self.saved_midi_out_port = midi_out_name
            self.save_config()
            self.osc_server_thread = threading.Thread(target=self.start_async_server_thread, args=(osc_in_port,), daemon=True)
            self.osc_server_thread.start()
            self.bi_dir_button.config(text="Stop and Close")
            self.obs_button.config(text="Stop and Close")
            self.log_message("OBS OSC Server started (async).")
            self.set_connection_status("green")
        else:
            self.quit_app()

    # ---------------- OSC Server Functions ----------------
    def is_port_in_use(self, port: int) -> bool:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            try:
                s.bind(("0.0.0.0", port))
                return False
            except OSError:
                return True

    def start_osc_server_thread(self, port: int) -> None:
        disp = dispatcher.Dispatcher()
        # Map static incoming addresses
        disp.map(self.osc_addresses_in["pause"], self.handle_pause)
        disp.map(self.osc_addresses_in["play"], self.handle_play)
        disp.map(self.osc_addresses_in["skip"], self.handle_skip)
        disp.map(self.osc_addresses_in["back"], self.handle_back)
        disp.map(self.osc_addresses_in["previous"], self.handle_previous)
        disp.map(self.osc_addresses_in["bpm"], self.handle_bpm)
        disp.map(self.osc_addresses_in["bpm1"], self.handle_bpm1_toggle)
        disp.map(self.osc_addresses_in["resetbpm"], self.handle_resetbpm)
        disp.map(self.osc_addresses_in["generic"], self.handle_osc_generic)
        # Map dynamic incoming addresses: note, noteoff, cc, pitch, after
        for ch in range(1, 17):
            disp.map(f"/note{ch}", self.handle_osc_note_dynamic)
            disp.map(f"/noteoff{ch}", self.handle_osc_noteoff_dynamic)
            disp.map(f"/cc{ch}", self.handle_osc_cc_dynamic)
            disp.map(f"/pitch{ch}", self.handle_osc_pitch_dynamic)
            disp.map(f"/after{ch}", self.handle_osc_after_dynamic)
        # Map numeric addresses for track skipping
        for i in range(1, 51):
            disp.map(f"/{i}", self.handle_numeric_skip)

        # Map the Note Off Delay address from the UI (default "/delay")
        disp.map(self.note_off_delay_address_entry.get(), self.handle_set_note_off_delay)

        try:
            self.osc_server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", port), disp)
            self.log_message(f"OSC Server bound to port {port}.")
            self.set_connection_status("green")
            self.osc_server.serve_forever()
        except OSError as e:
            self.log_message(f"OSC Server bind error: {e}", level=logging.ERROR)
            messagebox.showerror("Binding Error", f"Could not bind to port {port}: {e}")
            self.set_connection_status("red")

    def start_async_server_thread(self, port: int) -> None:
        async def server_coroutine():
            disp = dispatcher.Dispatcher()
            disp.map(self.osc_addresses_in["pause"], self.handle_pause)
            disp.map(self.osc_addresses_in["play"], self.handle_play)
            disp.map(self.osc_addresses_in["skip"], self.handle_skip)
            disp.map(self.osc_addresses_in["back"], self.handle_back)
            disp.map(self.osc_addresses_in["previous"], self.handle_previous)
            disp.map(self.osc_addresses_in["bpm"], self.handle_bpm)
            disp.map(self.osc_addresses_in["bpm1"], self.handle_bpm1_toggle)
            disp.map(self.osc_addresses_in["resetbpm"], self.handle_resetbpm)
            disp.map(self.osc_addresses_in["generic"], self.handle_osc_generic)
            for ch in range(1, 17):
                disp.map(f"/note{ch}", self.handle_osc_note_dynamic)
                disp.map(f"/noteoff{ch}", self.handle_osc_noteoff_dynamic)
                disp.map(f"/cc{ch}", self.handle_osc_cc_dynamic)
                disp.map(f"/pitch{ch}", self.handle_osc_pitch_dynamic)
                disp.map(f"/after{ch}", self.handle_osc_after_dynamic)
            for i in range(1, 51):
                disp.map(f"/{i}", self.handle_numeric_skip)

            # Also map the Note Off Delay address
            disp.map(self.note_off_delay_address_entry.get(), self.handle_set_note_off_delay)

            try:
                server = osc_server.AsyncIOOSCUDPServer(("0.0.0.0", port), disp, asyncio.get_running_loop())
                transport, protocol = await server.create_serve_endpoint()
                self.log_message(f"Async OSC Server bound to port {port}.")
                self.set_connection_status("green")
                while True:
                    await asyncio.sleep(1)
            except Exception as e:
                self.log_message(f"Async OSC Server error: {e}", level=logging.ERROR)
                self.set_connection_status("red")

        asyncio.run(server_coroutine())

    def set_connection_status(self, color: str) -> None:
        if color not in ["red", "green"]:
            color = "red"
        self.master.after(0, lambda: self.connection_indicator.itemconfig(self.indicator, fill=color))

    def handle_numeric_skip(self, address, *args):
        m = re.match(r'^/(\d+)$', address)
        if m:
            num = int(m.group(1))
            self.skip_to_number(num)
        else:
            self.log_message(f"Unhandled numeric OSC address: {address}")

    # ---------------- Handler for setting Note Off Delay via OSC ----------------
    def handle_set_note_off_delay(self, address, *args):
        """Allows changing the Note Off Delay slider via an OSC message."""
        if len(args) < 1:
            return
        try:
            val = float(args[0])
        except ValueError:
            return
        val = max(0, min(5, val))  # clamp to [0..5]
        self.note_off_delay_slider.set(val)
        self.note_off_delay = val
        self.log_message(f"Note Off Delay set via OSC to {val} sec")

    # ---------------- Static OSC Handlers ----------------
    def handle_bpm1_toggle(self, address, *args):
        current = self.ignore_bpm_var.get()
        new_val = not current
        self.ignore_bpm_var.set(new_val)
        self.log_message(f"'{self.osc_addresses_in.get('bpm1')}' toggled -> ignoring /bpm = {new_val}")

    def handle_resetbpm(self, address, *args):
        if not self.playing:
            self.log_message("Received /resetbpm but no playback active.")
            return
        self.user_bpm = max(1, round(self.default_bpm))
        self.smoothed_bpm = float(self.user_bpm)
        self.bpm_slider.set(self.user_bpm)
        self.log_message("BPM reset to default from MIDI file.")

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
            self.log_message("Skip requested but no playback active.")

    def handle_back(self, address, *args):
        if self.playing:
            self.back_event.set()
            self.log_message("Back requested (OSC).")
        else:
            self.log_message("Back requested but no playback active.")

    def handle_bpm(self, address, *args):
        if self.bpm_locked or self.ignore_bpm_var.get():
            self.log_message(f"Received {address} but BPM updates are locked/ignored.")
            return
        now_ts = time.time()
        self.bpm_tick_times.append(now_ts)
        if len(self.bpm_tick_times) > 4:
            self.bpm_tick_times.pop(0)
        if len(self.bpm_tick_times) == 4:
            intervals = [self.bpm_tick_times[i+1]-self.bpm_tick_times[i] for i in range(3)]
            avg_int = sum(intervals)/len(intervals)
            new_bpm = 60.0/avg_int
            self.smoothed_bpm = (self.alpha*new_bpm)+((1-self.alpha)*self.smoothed_bpm)
            final_bpm = max(1, round(self.smoothed_bpm))
            self.user_bpm = final_bpm
            self.master.after(0, lambda: self.bpm_slider.set(final_bpm))
            self.log_message(f"{address} -> {final_bpm} BPM")

    # ---------------- CC Controls ----------------
    def send_cc_message(self, idx: int) -> None:
        addr = self.cc_address_entries[idx].get().strip()
        val = self.cc_sliders[idx].get()
        if not addr.startswith("/"):
            messagebox.showerror("Invalid OSC Address", f"OSC address for CC {idx+1} must start with '/'.")
            return
        if self.osc_client:
            try:
                self.osc_client.send_message(addr, val)
                self.log_message(f"Sent OSC -> {addr} with value {val}")
            except Exception as e:
                self.log_message(f"Error sending OSC to {addr}: {e}", level=logging.ERROR)
        else:
            self.log_message("OSC Client not connected; CC not sent.", level=logging.ERROR)

    # ---------------- BPM & Tempo ----------------
    def update_bpm(self, new_bpm_str) -> None:
        if self.bpm_locked:
            return
        try:
            new_bpm = float(new_bpm_str)
            self.smoothed_bpm = (self.alpha*new_bpm)+((1-self.alpha)*self.smoothed_bpm)
            final_bpm = max(1, round(self.smoothed_bpm))
            self.user_bpm = final_bpm
            self.bpm_slider.set(final_bpm)
            self.log_message(f"User BPM set to {final_bpm}")
        except ValueError:
            pass

    def reset_bpm(self) -> None:
        self.user_bpm = max(1, round(self.default_bpm))
        self.smoothed_bpm = float(self.user_bpm)
        self.bpm_slider.set(self.user_bpm)
        self.log_message(f"Tempo reset to {self.user_bpm} BPM")

    def toggle_lock_bpm(self) -> None:
        self.bpm_locked = not self.bpm_locked
        if self.bpm_locked:
            self.bpm_slider.config(state="disabled")
            self.lock_bpm_button.config(text="Unlock Tempo")
            self.log_message("BPM slider locked.")
        else:
            self.bpm_slider.config(state="normal")
            self.lock_bpm_button.config(text="Lock Tempo")
            self.log_message("BPM slider unlocked.")

    def toggle_ignore_bpm(self) -> None:
        if self.ignore_bpm_var.get():
            self.log_message("Ignoring incoming /bpm messages.")
        else:
            self.log_message("Processing incoming /bpm messages.")

    # ---------------- BPM Sync ----------------
    def toggle_sync(self) -> None:
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

    def _sync_loop(self) -> None:
        while not self.sync_stop_event.is_set() and self.sync_var.get():
            current = max(1, round(self.user_bpm))
            delay = 60.0/current
            time.sleep(delay)
            if self.sync_stop_event.is_set() or not self.sync_var.get():
                break
            if self.osc_client:
                self.osc_client.send_message(self.osc_addresses_out.get("sync", "/sync"), current)
                self.log_message(f"Sent OSC -> {self.osc_addresses_out.get('sync', '/sync')} at BPM {current}")

    # ---------------- MIDI Input Loop ----------------
    def run_midi_loop(self, midi_in) -> None:
        while True:
            for msg in midi_in.iter_pending():
                self.handle_midi_message(msg, source="input")
            time.sleep(0.01)

    # ---------------- Addresses Editor ----------------
    def open_addresses_editor(self) -> None:
        # Create a new Toplevel window.
        editor = tk.Toplevel(self.master)
        editor.title("Edit OSC Addresses")
        editor.geometry("600x400")
        editor.resizable(True, True)
        # Create a canvas with vertical scrollbar.
        canvas = tk.Canvas(editor, bg="#2B2B2B")
        scrollbar = ttk.Scrollbar(editor, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        # Create a frame inside the canvas.
        frame = ttk.Frame(canvas)
        frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=frame, anchor="nw")
        # At the very top-right, create a frame for Save and Reset buttons (stacked vertically).
        top_btn_frame = ttk.Frame(frame)
        top_btn_frame.grid(row=0, column=1, sticky="ne", padx=5, pady=5)
        ttk.Button(top_btn_frame, text="Save Edit",
                   command=lambda: self.save_addresses(editor, static_in_entries, static_out_entries, dynamic_entries)
                   ).pack(pady=(0,5))
        ttk.Button(top_btn_frame, text="Reset to Default",
                   command=lambda: self.reset_addresses(static_in_entries, static_out_entries, dynamic_entries)
                   ).pack()
        # Now create the Notebook for the address fields.
        nb = ttk.Notebook(frame)
        nb.grid(row=1, column=0, columnspan=2, padx=10, pady=10, sticky="nsew")
        static_in_frame = ttk.Frame(nb)
        nb.add(static_in_frame, text="Static Incoming")
        static_out_frame = ttk.Frame(nb)
        nb.add(static_out_frame, text="Static Outgoing")
        dynamic_frame = ttk.Frame(nb)
        nb.add(dynamic_frame, text="Dynamic (Template)")

        static_in_entries = {}
        static_out_entries = {}
        dynamic_templates = {
            "Note": self.osc_addresses_in.get("noteX", "/noteX"),
            "NoteOff": self.osc_addresses_in.get("noteoffX", "/noteoffX"),
            "CC": self.osc_addresses_in.get("ccX", "/ccX"),
            "Pitch": self.osc_addresses_in.get("pitchX", "/pitchX"),
            "Aftertouch": self.osc_addresses_in.get("afterX", "/afterX")
        }
        dynamic_entries = {}

        # For static_in, exclude the ones ending with X.
        def create_fields(frm, data, entries):
            for idx, (key, addr) in enumerate(data.items()):
                ttk.Label(frm, text=f"{key}:").grid(row=idx, column=0, sticky=tk.W, padx=5, pady=5)
                ent = ttk.Entry(frm, width=30)
                ent.grid(row=idx, column=1, sticky=tk.W, padx=5, pady=5)
                ent.insert(0, addr)
                entries[key] = ent

        # Filter out dynamic (X) from static_in
        static_in = {k: v for k, v in self.osc_addresses_in.items()
                     if not k.endswith("X") and k not in ["afterX", "pitchX"]}
        create_fields(static_in_frame, static_in, static_in_entries)

        # For static_out, we only have "sync"
        create_fields(static_out_frame, self.osc_addresses_out, static_out_entries)

        # Dynamic
        create_fields(dynamic_frame, dynamic_templates, dynamic_entries)

    def save_addresses(self, window, static_in, static_out, dynamic):
        for k, ent in static_in.items():
            addr = ent.get().strip()
            if not addr.startswith("/"):
                messagebox.showerror("Invalid Address", f"Address for {k} must start with '/'.")
                return
            self.osc_addresses_in[k] = addr
        for k, ent in static_out.items():
            addr = ent.get().strip()
            if not addr.startswith("/"):
                messagebox.showerror("Invalid Address", f"Address for {k} must start with '/'.")
                return
            self.osc_addresses_out[k] = addr
        for k, ent in dynamic.items():
            addr = ent.get().strip()
            if not addr.startswith("/"):
                messagebox.showerror("Invalid Address", f"Dynamic address for {k} must start with '/'.")
                return
            if k.lower() == "note":
                self.osc_addresses_in["noteX"] = addr
            elif k.lower() == "noteoff":
                self.osc_addresses_in["noteoffX"] = addr
            elif k.lower() == "cc":
                self.osc_addresses_in["ccX"] = addr
            elif k.lower() == "pitch":
                self.osc_addresses_in["pitchX"] = addr
            elif k.lower() == "aftertouch":
                self.osc_addresses_in["afterX"] = addr
        self.save_config()
        self.log_message("OSC Addresses updated and saved.")
        messagebox.showinfo("Success", "OSC Addresses updated.")
        window.destroy()

    def reset_addresses(self, static_in, static_out, dynamic):
        for k, ent in static_in.items():
            default = self.default_osc_addresses_in.get(k, "")
            ent.delete(0, tk.END)
            ent.insert(0, default)
            self.osc_addresses_in[k] = default

        for k, ent in static_out.items():
            default = self.default_osc_addresses_out.get(k, "")
            ent.delete(0, tk.END)
            ent.insert(0, default)
            self.osc_addresses_out[k] = default

        defaults = {
            "Note": "/noteX",
            "NoteOff": "/noteoffX",
            "CC": "/ccX",
            "Pitch": "/pitchX",
            "Aftertouch": "/afterX"
        }
        for k, ent in dynamic.items():
            default = defaults.get(k, "")
            ent.delete(0, tk.END)
            ent.insert(0, default)
            if k.lower() == "note":
                self.osc_addresses_in["noteX"] = default
            elif k.lower() == "noteoff":
                self.osc_addresses_in["noteoffX"] = default
            elif k.lower() == "cc":
                self.osc_addresses_in["ccX"] = default
            elif k.lower() == "pitch":
                self.osc_addresses_in["pitchX"] = default
            elif k.lower() == "aftertouch":
                self.osc_addresses_in["afterX"] = default

        self.save_config()
        self.log_message("OSC Addresses reset to default.")
        messagebox.showinfo("Reset", "OSC Addresses reset to default.")

    # ---------------- Show Help ----------------
    def show_help(self) -> None:
        help_win = tk.Toplevel(self.master)
        help_win.title("Help - OSC Commands")
        help_win.geometry("500x700")
        help_win.resizable(False, False)
        help_win.transient(self.master)
        help_win.grab_set()
        text = tk.Text(help_win, wrap="word", bg="#2B2B2B", fg="#FFFFFF", font=("Courier", 10))
        text.pack(expand=True, fill="both", padx=10, pady=10)
        help_text = f"""
------ OSC Addresses (Incoming) ------
Static (editable):
  pause: {self.osc_addresses_in.get("pause", "/pause")}
  play: {self.osc_addresses_in.get("play", "/play")}
  skip: {self.osc_addresses_in.get("skip", "/skip")}
  back: {self.osc_addresses_in.get("back", "/back")}
  previous: {self.osc_addresses_in.get("previous", "/previous")}
  bpm: {self.osc_addresses_in.get("bpm", "/bpm")}
  bpm1: {self.osc_addresses_in.get("bpm1", "/bpm1")}
  resetbpm: {self.osc_addresses_in.get("resetbpm", "/resetbpm")}
  generic: {self.osc_addresses_in.get("generic", "/generic")}

Dynamic Incoming (Template):
  /noteX         (for note_on messages)
  /noteoffX      (for note_off messages)
  /ccX           (for control change messages)
  /pitchX        (for pitchbend messages)
  /afterX        (for aftertouch messages)

------ OSC Addresses (Outgoing) ------
Static (editable):
  sync: {self.osc_addresses_out.get("sync", "/sync")}

Dynamic Outgoing (automatic by channel):
  note_on  --> /noteX
  note_off --> /noteoffX
  cc       --> /ccX
  pitchwheel --> /pitchX
  aftertouch --> /afterX

Example OSC Commands:
  /note5 60 0.8         --> MIDI note_on on channel 5, velocity ~102, auto note_off after slider delay.
  /noteoff5 60 0        --> MIDI note_off on channel 5.
  /cc3 10 0.5           --> MIDI control_change on channel 3, cc=10, value=~63.
  /pitch2 4096          --> MIDI pitchbend on channel 2.
  /after2 64            --> MIDI aftertouch on channel 2.
  /generic "note_on" 60 0.8  --> Converts OSC to MIDI note_on (default channel).
  /delay 1.2            --> Sets the Note Off Delay to 1.2s via OSC.
"""
        text.insert("1.0", help_text)
        text.config(state="disabled")

    # ---------------- UI Toggles ----------------
    def toggle_midi_menu(self) -> None:
        if self.alarm_frame_visible:
            self.alarm_frame.pack_forget()
            self.alarm_frame_visible = False
            self.alarm_menu_button.config(text="≡ Alarm Clock")
        if self.cc_frame_visible:
            self.cc_frame.pack_forget()
            self.cc_frame_visible = False
            self.cc_menu_button.config(text="≡ CC")
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

    def toggle_alarm_menu(self) -> None:
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

    def toggle_cc_menu(self) -> None:
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

    # ---------------- Connection / Cleanup ----------------
    def quit_app(self) -> None:
        try:
            if self.midi_out:
                self.midi_out.close()
        except Exception as e:
            logging.debug(f"Error closing MIDI output: {e}")
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
            if self.osc_server:
                self.osc_server.shutdown()
                self.osc_server = None
                self.set_connection_status("red")
                self.log_message("OSC Server stopped.")
            self.master.quit()

    # ---------------- Display OSC Addresses ----------------
    def display_osc_addresses(self) -> None:
        self.log_message("------ OSC Addresses ------")
        self.log_message("Static Incoming:")
        for k, v in self.osc_addresses_in.items():
            if not k.endswith("X"):
                self.log_message(f"  {k}: {v}")
        self.log_message("Static Outgoing:")
        for k, v in self.osc_addresses_out.items():
            self.log_message(f"  {k}: {v}")
        self.log_message("Dynamic Incoming (Template):")
        self.log_message("  /noteX         (for note_on messages)")
        self.log_message("  /noteoffX      (for note_off messages)")
        self.log_message("  /ccX           (for control change messages)")
        self.log_message("  /pitchX        (for pitchbend messages)")
        self.log_message("  /afterX        (for aftertouch messages)")
        self.log_message("------------------------------")

    # ---------------- Wrapper for Previous ----------------
    def handle_previous(self, *args):
        self.previous()

# ---------------- Main Execution ----------------
if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("500x420")
    app = OSCMIDIApp(root)
    root.protocol("WM_DELETE_WINDOW", app.quit_app)
    root.mainloop()

