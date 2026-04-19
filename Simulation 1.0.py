import os
import json
import random
import time
import requests
import math
from typing import List, Dict, Tuple
import plotly.graph_objects as go
import plotly.express as px  # Import plotly.express for animations
import pandas as pd  # Import pandas for data manipulation
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
import webbrowser # Import for opening the HTML map

# ==== Konstanta Global ====
# !!! GANTI DENGAN API KEY TOMTOM ANDA YANG VALID !!!
API_KEY = "RnJCaznKckvWSLQct8JJ8ee2HayDhQwS" # Contoh: "RnJCaznKckvWSLQct8JJ8ee2HayDhQwS"
TARIF_BBM = 13000  # Rp/liter
GAJI_SOPIR_PER_JAM = 30000  # Rp
BIAYA_PEMELIHARAAN_PER_TRIP = 100000  # Rp
ITERASI_DEFAULT = 3 # Default jumlah rute alternatif/iterasi untuk simulasi
ANIMATION_TIME_STEP_MIN = 5 # Langkah waktu animasi dalam menit

# ==== Koordinat Kota ====
KOTA_KOORDINAT = {
    "Jakarta": (-6.200000, 106.816666),
    "Bandung": (-6.914864, 107.608238)
}

# ==== Fungsi Perhitungan Jarak (Haversine) - Digunakan untuk interpolasi di prepare_animation_data ====
def calculate_haversine_distance(lat1, lon1, lat2, lon2) -> float:
    R = 6371  # Radius Bumi dalam kilometer
    lat1_rad = math.radians(lat1)
    lon1_rad = math.radians(lon1)
    lat2_rad = math.radians(lat2)
    lon2_rad = math.radians(lon2)

    dlat = lat2_rad - lat1_rad
    dlon = lon2_rad - lon1_rad

    a = math.sin(dlat / 2)**2 + math.cos(lat1_rad) * math.cos(lat2_rad) * math.sin(dlon / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))

    distance = R * c
    return distance # Jarak dalam kilometer

# ==== Fungsi API TomTom ====
def get_routing_data(from_coord: Tuple[float, float], to_coord: Tuple[float, float], avoid_traffic: bool = True) -> Dict:
    if API_KEY == "YOUR_TOMTOM_API_KEY_HERE":
        messagebox.showerror("Error", "Mohon ganti 'YOUR_TOMTOM_API_KEY_HERE' dengan API Key TomTom Anda yang valid.")
        return {}

    url = f"https://api.tomtom.com/routing/1/calculateRoute/{from_coord[0]},{from_coord[1]}:{to_coord[0]},{to_coord[1]}/json"
    params = {
        "key": API_KEY,
        "traffic": "true" if avoid_traffic else "false", # traffic bisa dinamis berdasarkan skenario
        "travelMode": "truck",
        "routeType": "fastest",
        "computeBestOrder": "false",
        "maxAlternatives": 3 # Mengambil hingga 3 rute alternatif
    }
    try:
        response = requests.get(url, params=params)
        response.raise_for_status() # Raise an HTTPError for bad responses (4xx or 5xx)
        return response.json()
    except requests.exceptions.RequestException as e:
        messagebox.showerror("Error API", f"Gagal mengambil rute dari TomTom API: {e}. Periksa koneksi internet dan API Key.")
        return {}

# ==== Fungsi Simulasi Pengiriman ====
def simulate_trip(route: Dict) -> Dict:
    summary = route["summary"]
    travel_time_sec = summary["travelTimeInSeconds"]
    travel_time_min = travel_time_sec / 60
    travel_time_hour = travel_time_min / 60
    distance_km = summary["lengthInMeters"] / 1000

    # Kebutuhan bahan bakar per truk menggunakan distribusi Uniform (3,6) liter per jam. [cite: 9]
    konsumsi_bbm_per_hour = random.uniform(3, 6)
    fuel_liters = konsumsi_bbm_per_hour * travel_time_hour
    biaya_bbm = fuel_liters * TARIF_BBM
    biaya_sopir = travel_time_hour * GAJI_SOPIR_PER_JAM
    biaya_total = biaya_bbm + biaya_sopir + BIAYA_PEMELIHARAAN_PER_TRIP

    return {
        "travel_time_min": travel_time_min,
        "distance_km": distance_km,
        "fuel_liters": fuel_liters,
        "biaya_total": biaya_total
    }

# ==== Fungsi Visualisasi Peta Statis ====
def save_route_map_html(routes: List[Dict], filename="simulasi_rute_truk_statis.html"):
    fig = go.Figure()
    colors = ["red", "blue", "green", "orange", "purple", "brown"] # Warna untuk rute

    for i, route in enumerate(routes):
        if "legs" in route and len(route["legs"]) > 0 and "points" in route["legs"][0]:
            points = route["legs"][0]["points"]
            lats = [pt["latitude"] for pt in points]
            lons = [pt["longitude"] for pt in points]
            fig.add_trace(go.Scattergeo(
                locationmode='country names',
                lon=lons,
                lat=lats,
                mode='lines',
                line=dict(width=3, color=colors[i % len(colors)]),
                name=f"Rute {i+1}",
                hoverinfo='text',
                text=[f"Rute {i+1}<br>Jarak: {route['summary']['lengthInMeters']/1000:.2f} km<br>Waktu: {route['summary']['travelTimeInSeconds']/60:.2f} menit"] * len(lats)
            ))
        else:
            print(f"Peringatan: Rute {i+1} tidak memiliki data 'legs' atau 'points' yang diharapkan.")

    # Tambahkan titik awal dan akhir
    if routes:
        first_route_points = routes[0]["legs"][0]["points"]
        start_coord = (first_route_points[0]["latitude"], first_route_points[0]["longitude"])
        end_coord = (first_route_points[-1]["latitude"], first_route_points[-1]["longitude"])

        fig.add_trace(go.Scattergeo(
            locationmode='country names',
            lon=[start_coord[1], end_coord[1]],
            lat=[start_coord[0], end_coord[0]],
            mode='markers',
            marker=dict(size=10, color='black', symbol='circle'),
            name='Mulai/Akhir',
            hoverinfo='text',
            text=["Titik Awal", "Titik Akhir"]
        ))

    all_lats = []
    all_lons = []
    for route in routes:
        if "legs" in route and len(route["legs"]) > 0 and "points" in route["legs"][0]:
            all_lats.extend([pt["latitude"] for pt in route["legs"][0]["points"]])
            all_lons.extend([pt["longitude"] for pt in route["legs"][0]["points"]])

    if all_lats and all_lons:
        lataxis_range = [min(all_lats) - 0.5, max(all_lats) + 0.5]
        lonaxis_range = [min(all_lons) - 0.5, max(all_lons) + 0.5]
    else:
        lataxis_range = [-10, 0]
        lonaxis_range = [100, 115]

    fig.update_layout(
        title="Visualisasi Rute Simulasi Truk (Statis)",
        geo=dict(
            scope='asia',
            projection_type='equirectangular',
            showland=True,
            landcolor="rgb(243, 243, 243)",
            countrycolor="rgb(204, 204, 204)",
            lataxis_range=lataxis_range,
            lonaxis_range=lonaxis_range
        ),
        hovermode='closest'
    )
    fig.write_html(filename)
    return filename

# ==== Fungsi untuk Menyiapkan Data Animasi ====
def prepare_animation_data(routes: List[Dict], time_step_min: int = ANIMATION_TIME_STEP_MIN) -> pd.DataFrame:
    animation_frames = []
    
    for i, route in enumerate(routes):
        route_index = i + 1
        points = route["legs"][0]["points"]
        total_travel_time_sec = route["summary"]["travelTimeInSeconds"]
        total_travel_time_min = total_travel_time_sec / 60

        # Hitung waktu kumulatif untuk setiap titik di rute
        cumulative_times = [0]
        for j in range(1, len(points)):
            # Perkirakan waktu per segmen berdasarkan proporsi jarak dan total waktu
            dist_segment = calculate_haversine_distance(
                points[j-1]["latitude"], points[j-1]["longitude"],
                points[j]["latitude"], points[j]["longitude"]
            )
            # Ini adalah perkiraan waktu per segmen, perlu total jarak untuk proporsi
            # Lebih baik jika API menyediakan waktu per segmen
            # Untuk sementara, gunakan proporsi jarak relatif terhadap total rute
            
            # Mendapatkan total jarak rute dari API, jika ada
            # Jika tidak ada, gunakan jarak Haversine total dari titik awal ke akhir
            total_route_distance_km = route["summary"]["lengthInMeters"] / 1000

            time_for_segment = (dist_segment / total_route_distance_km) * total_travel_time_min if total_route_distance_km > 0 else 0
            cumulative_times.append(cumulative_times[-1] + time_for_segment)
        
        # Normalisasi cumulative_times agar totalnya sesuai dengan travel_time_min
        if cumulative_times[-1] > 0:
            scale_factor = total_travel_time_min / cumulative_times[-1]
            cumulative_times = [t * scale_factor for t in cumulative_times]
        else:
            cumulative_times = [0] * len(points)


        # Buat frame animasi
        current_time_frame = 0
        max_frame_time = max(cumulative_times) if cumulative_times else 0

        while current_time_frame <= max_frame_time + time_step_min: # Tambahan kecil untuk memastikan titik akhir masuk
            # Cari posisi lat/lon pada current_time_frame
            # Cari dua titik polyline di mana current_time_frame berada di antaranya
            idx1 = 0
            while idx1 < len(cumulative_times) - 1 and cumulative_times[idx1+1] < current_time_frame:
                idx1 += 1
            
            lat, lon = 0, 0
            if idx1 == len(cumulative_times) - 1: # Sudah di titik akhir atau setelahnya
                lat = points[-1]["latitude"]
                lon = points[-1]["longitude"]
            else:
                time_diff = cumulative_times[idx1+1] - cumulative_times[idx1]
                if time_diff > 0:
                    ratio = (current_time_frame - cumulative_times[idx1]) / time_diff
                else:
                    ratio = 0 # Jika waktu segmen 0, berarti di titik yang sama

                lat = points[idx1]["latitude"] + (points[idx1+1]["latitude"] - points[idx1]["latitude"]) * ratio
                lon = points[idx1]["longitude"] + (points[idx1+1]["longitude"] - points[idx1]["longitude"]) * ratio
            
            animation_frames.append({
                'route_id': f"Rute {route_index}",
                'latitude': lat,
                'longitude': lon,
                'time_min': current_time_frame,
                'frame_id': int(current_time_frame / time_step_min)
            })
            current_time_frame += time_step_min
        
        # Pastikan titik akhir selalu ada di frame terakhir untuk rute tersebut
        # Ini penting agar truk tidak "menghilang" sebelum mencapai tujuan
        if total_travel_time_min not in [f['time_min'] for f in animation_frames if f['route_id'] == f"Rute {route_index}"]:
             animation_frames.append({
                'route_id': f"Rute {route_index}",
                'latitude': points[-1]["latitude"],
                'longitude': points[-1]["longitude"],
                'time_min': total_travel_time_min,
                'frame_id': int(total_travel_time_min / time_step_min)
            })


    df = pd.DataFrame(animation_frames)
    # Penting: Pastikan frame_id dan time_min diurutkan dengan benar
    # `rank(method='dense')` untuk memastikan frame_id berurutan 0, 1, 2...
    df['frame_id'] = df.groupby('route_id')['time_min'].rank(method='dense').astype(int) -1
    df = df.sort_values(by=['frame_id', 'route_id']).reset_index(drop=True)
    return df

# ==== Fungsi untuk Menyimpan Peta Animasi HTML ====
def save_animated_map_html(
    animation_df: pd.DataFrame,
    routes: List[Dict],
    filename="simulasi_rute_truk_animasi.html"
):
    fig = go.Figure()
    colors = ["red", "blue", "green", "orange", "purple", "brown"] # Warna untuk rute statis

    # Tambahkan semua rute sebagai garis statis di latar belakang
    for i, route in enumerate(routes):
        if "legs" in route and len(route["legs"]) > 0 and "points" in route["legs"][0]:
            points = route["legs"][0]["points"]
            lats = [pt["latitude"] for pt in points]
            lons = [pt["longitude"] for pt in points]
            fig.add_trace(go.Scattergeo(
                locationmode='country names',
                lon=lons,
                lat=lats,
                mode='lines',
                line=dict(width=2, color=colors[i % len(colors)], dash='dot'), # Garis putus-putus
                name=f"Rute {i+1} (Dasar)",
                opacity=0.7,
                showlegend=True
            ))

    # Tambahkan titik awal dan akhir secara statis
    if routes:
        first_route_points = routes[0]["legs"][0]["points"]
        start_coord = (first_route_points[0]["latitude"], first_route_points[0]["longitude"])
        end_coord = (first_route_points[-1]["latitude"], first_route_points[-1]["longitude"])

        fig.add_trace(go.Scattergeo(
            locationmode='country names',
            lon=[start_coord[1], end_coord[1]],
            lat=[start_coord[0], end_coord[0]],
            mode='markers',
            marker=dict(size=10, color='black', symbol='circle'),
            name='Mulai/Akhir',
            hoverinfo='text',
            text=["Titik Awal", "Titik Akhir"],
            showlegend=True
        ))

    # Buat figure untuk animasi menggunakan px.scatter_geo
    if not animation_df.empty:
        animated_scatter = px.scatter_geo(
            animation_df,
            lat="latitude",
            lon="longitude",
            animation_frame="frame_id",
            animation_group="route_id",
            color="route_id",
            size_max=10,
            opacity=1.0,
            symbol="route_id", # Simbol berbeda untuk setiap truk
            hover_name="route_id",
            hover_data={"time_min": ":.0f", "latitude": False, "longitude": False}, # Format time_min
            projection="equirectangular",
            scope='asia',
        )
        
        fig.frames = animated_scatter.frames # Transfer frames dari animated_scatter ke fig utama
        
        # Tambahkan trace animasi pertama (untuk frame_id 0) ke fig utama sebagai tampilan awal
        fig.add_trace(animated_scatter.data[0])

    all_lats_combined = []
    all_lons_combined = []
    for route in routes:
        if "legs" in route and len(route["legs"]) > 0 and "points" in route["legs"][0]:
            all_lats_combined.extend([pt["latitude"] for pt in route["legs"][0]["points"]])
            all_lons_combined.extend([pt["longitude"] for pt in route["legs"][0]["points"]])
    
    if all_lats_combined and all_lons_combined:
        lataxis_range = [min(all_lats_combined) - 0.5, max(all_lats_combined) + 0.5]
        lonaxis_range = [min(all_lons_combined) - 0.5, max(all_lons_combined) + 0.5]
    else:
        lataxis_range = [-10, 0] # Default for Indonesia
        lonaxis_range = [100, 115]


    fig.update_layout(
        title="Animasi Perjalanan Truk per Iterasi",
        geo=dict(
            scope='asia',
            projection_type='equirectangular',
            showland=True,
            landcolor="rgb(243, 243, 243)",
            countrycolor="rgb(204, 204, 204)",
            lataxis_range=lataxis_range,
            lonaxis_range=lonaxis_range
        ),
        hovermode='closest',
        updatemenus=[dict(
            type="buttons",
            buttons=[dict(label="Play",
                          method="animate",
                          args=[None, {"frame": {"duration": 100, "redraw": True}, "fromcurrent": True, "transition": {"duration": 50, "easing": "linear"}}])]
        )],
        sliders=[dict(
            steps=[
                dict(args=[[f.name], dict(mode='immediate', frame=dict(duration=100, redraw=True), transition=dict(duration=50))],
                     label=f.name)
                for f in fig.frames
            ],
            transition=dict(duration=50, easing="linear"),
            x=0.1,
            len=0.9,
            currentvalue=dict(font=dict(size=12), prefix="Waktu (menit): ", xanchor="right"),
            pad=dict(r=10, t=50),
            y=0
        )]
    )
    
    fig.write_html(filename, auto_play=False)
    return filename

# ==== Fungsi Utama Simulasi ====
def jalankan_simulasi(iterasi: int = ITERASI_DEFAULT, avoid_traffic: bool = True):
    from_kota, to_kota = "Jakarta", "Bandung"
    from_coord = KOTA_KOORDINAT[from_kota]
    to_coord = KOTA_KOORDINAT[to_kota]
    data_routing = get_routing_data(from_coord, to_coord, avoid_traffic=avoid_traffic)

    if not data_routing or "routes" not in data_routing:
        return [], None, None # Mengembalikan nilai null untuk file map

    routes_to_simulate = data_routing["routes"][:iterasi]
    hasil_simulasi = []

    for idx, route in enumerate(routes_to_simulate):
        hasil = simulate_trip(route)
        hasil["route_index"] = idx + 1
        hasil_simulasi.append(hasil)

    map_file_static = save_route_map_html(routes_to_simulate)
    animation_df = prepare_animation_data(routes_to_simulate)
    map_file_animated = save_animated_map_html(animation_df, routes_to_simulate)

    return hasil_simulasi, map_file_static, map_file_animated

# ==== GUI Lokal Tkinter ====
class SimulasiApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Simulasi Sistem Transportasi Truk Nasional")
        self.geometry("900x650") # Ukuran jendela disesuaikan
        self.resizable(False, False)
        self.map_filepath_static = ""
        self.map_filepath_animated = ""
        self.create_widgets()

    def create_widgets(self):
        self.tabControl = ttk.Notebook(self)

        # Tab 1: Dashboard Kontrol Simulasi
        self.tab1 = ttk.Frame(self.tabControl)
        self.tabControl.add(self.tab1, text='Kontrol Simulasi')

        # Frame untuk pengaturan simulasi
        sim_frame = ttk.LabelFrame(self.tab1, text="Pengaturan Simulasi")
        sim_frame.pack(pady=10, padx=10, fill="x")

        ttk.Label(sim_frame, text="Jumlah Iterasi Rute (default: 3):", font=('Arial', 10, 'bold')).pack(pady=5)
        self.iterasi_entry = ttk.Entry(sim_frame, width=15)
        self.iterasi_entry.insert(0, str(ITERASI_DEFAULT))
        self.iterasi_entry.pack(pady=5)

        self.run_button = ttk.Button(sim_frame, text="Mulai Simulasi", command=self.start_simulation)
        self.run_button.pack(pady=10)

        # Frame untuk Peta
        map_frame = ttk.LabelFrame(self.tab1, text="Visualisasi Peta")
        map_frame.pack(pady=10, padx=10, fill="x")

        self.show_map_button_static = ttk.Button(map_frame, text="Tampilkan Peta Rute (Statis)", command=self.open_static_map, state=tk.DISABLED)
        self.show_map_button_static.pack(pady=5)

        self.show_map_button_animated = ttk.Button(map_frame, text="Tampilkan Animasi Peta Truk", command=self.open_animated_map, state=tk.DISABLED)
        self.show_map_button_animated.pack(pady=5)

        # Frame untuk Skenario Simulasi
        scenario_frame = ttk.LabelFrame(self.tab1, text="Jalankan Skenario Simulasi")
        scenario_frame.pack(pady=10, padx=10, fill="x")

        ttk.Button(scenario_frame, text="Jalankan Skenario 1 (Rute Tetap & Statis)", command=lambda: self.run_scenario(1)).pack(pady=3)
        ttk.Button(scenario_frame, text="Jalankan Skenario 2 (Rute Dinamis Real-Time)", command=lambda: self.run_scenario(2)).pack(pady=3)
        ttk.Button(scenario_frame, text="Jalankan Skenario 3 (Pengiriman Gabungan)", command=lambda: self.run_scenario(3)).pack(pady=3)
        ttk.Button(scenario_frame, text="Jalankan Skenario 4 (Penambahan Truk)", command=lambda: self.run_scenario(4)).pack(pady=3)
        
        # Tab 2: Visualisasi Peta (akan dialihkan ke browser)
        # Kita tidak membuat widget peta di sini karena akan membuka di browser
        self.tab2 = ttk.Frame(self.tabControl)
        self.tabControl.add(self.tab2, text='Visualisasi Peta')
        ttk.Label(self.tab2, text="Peta akan dibuka di browser default Anda setelah simulasi selesai.", font=('Arial', 10)).pack(pady=50)


        # Tab 3: Output Simulasi
        self.tab3 = ttk.Frame(self.tabControl)
        self.tabControl.add(self.tab3, text='Output Simulasi')

        self.output_label = ttk.Label(self.tab3, text="Hasil Simulasi:", font=('Arial', 10, 'bold'))
        self.output_label.pack(pady=5)

        self.output_text = tk.Text(self.tab3, height=25, width=90, wrap=tk.WORD, font=('Courier New', 9))
        self.output_text.pack(pady=10)
        self.scrollbar = ttk.Scrollbar(self.tab3, command=self.output_text.yview)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.output_text.config(yscrollcommand=self.scrollbar.set)

        self.tabControl.pack(expand=1, fill="both", padx=10, pady=10)

    def start_simulation(self):
        self.run_scenario(0) # 0 berarti simulasi biasa tanpa skenario spesifik
    
    def run_scenario(self, scenario_id: int):
        iterasi_input = self.iterasi_entry.get()
        try:
            iterasi = int(iterasi_input) if iterasi_input else ITERASI_DEFAULT
            if iterasi <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Error", "Jumlah iterasi harus angka positif.")
            return

        self.output_text.delete("1.0", tk.END)
        self.show_map_button_static.config(state=tk.DISABLED)
        self.show_map_button_animated.config(state=tk.DISABLED)

        scenario_name = ""
        avoid_traffic = True # Default untuk Skenario 2 dan simulasi normal

        if scenario_id == 0:
            scenario_name = "Simulasi Umum"
        elif scenario_id == 1:
            scenario_name = "Skenario 1: Rute Tetap & Penjadwalan Statis"
            avoid_traffic = False # Untuk skenario statis, bisa anggap tidak menghindar lalu lintas real-time
            messagebox.showinfo("Informasi Skenario", "Skenario 1 akan menggunakan rute statis (tidak mempertimbangkan lalu lintas real-time) dan simulasi waktu/biaya standar.")
        elif scenario_id == 2:
            scenario_name = "Skenario 2: Rute Dinamis dengan Sistem Pemantauan Real-Time"
            avoid_traffic = True # Mempertimbangkan lalu lintas real-time (default API)
            messagebox.showinfo("Informasi Skenario", "Skenario 2 akan menggunakan rute dinamis (mempertimbangkan lalu lintas real-time) dan simulasi waktu/biaya bervariasi.")
        elif scenario_id == 3:
            scenario_name = "Skenario 3: Strategi Pengiriman Gabungan"
            messagebox.showwarning("Fitur Belum Penuh", "Skenario 3 (Pengiriman Gabungan) memerlukan implementasi logika rute multi-tujuan yang lebih kompleks, saat ini hanya menjalankan simulasi dasar.")
            # Logika skenario 3 akan ditambahkan di fungsi jalankan_simulasi jika API mendukung
        elif scenario_id == 4:
            scenario_name = "Skenario 4: Penambahan Truk & Peningkatan Infrastruktur"
            messagebox.showwarning("Fitur Belum Penuh", "Skenario 4 (Penambahan Truk) memerlukan simulasi armada dan alokasi yang lebih kompleks, saat ini hanya menjalankan simulasi dasar.")
            # Logika skenario 4 akan ditambahkan di fungsi jalankan_simulasi jika API mendukung

        self.output_text.insert(tk.END, f"Menjalankan {scenario_name} dengan {iterasi} rute...\n\n")
        self.output_text.update_idletasks()

        # Panggil fungsi simulasi utama
        hasil, map_file_static, map_file_animated = jalankan_simulasi(iterasi, avoid_traffic=avoid_traffic)

        if hasil:
            self.map_filepath_static = map_file_static
            self.map_filepath_animated = map_file_animated
            self.show_map_button_static.config(state=tk.NORMAL)
            self.show_map_button_animated.config(state=tk.NORMAL)
            
            self.output_text.insert(tk.END, "--- Hasil Simulasi Per Iterasi ---\n\n")
            for data in hasil:
                self.output_text.insert(tk.END, f"Rute {data['route_index']}:\n")
                self.output_text.insert(tk.END, f"  Jarak tempuh: {data['distance_km']:.2f} km\n")
                self.output_text.insert(tk.END, f"  Waktu tempuh: {data['travel_time_min']:.2f} menit\n")
                self.output_text.insert(tk.END, f"  Konsumsi BBM: {data['fuel_liters']:.2f} liter\n")
                self.output_text.insert(tk.END, f"  Biaya total: Rp{data['biaya_total']:.0f}\n\n")
            
            self.output_text.insert(tk.END, "\n--- Ringkasan Simulasi ---\n")
            avg_distance = sum(d['distance_km'] for d in hasil) / len(hasil)
            avg_time = sum(d['travel_time_min'] for d in hasil) / len(hasil)
            avg_fuel = sum(d['fuel_liters'] for d in hasil) / len(hasil)
            avg_cost = sum(d['biaya_total'] for d in hasil) / len(hasil)

            self.output_text.insert(tk.END, f"Jarak Tempuh Rata-rata: {avg_distance:.2f} km\n")
            self.output_text.insert(tk.END, f"Waktu Tempuh Rata-rata: {avg_time:.2f} menit\n")
            self.output_text.insert(tk.END, f"Konsumsi BBM Rata-rata: {avg_fuel:.2f} liter\n")
            self.output_text.insert(tk.END, f"Biaya Total Rata-rata: Rp{avg_cost:.0f}\n")

            messagebox.showinfo("Simulasi Selesai", f"{scenario_name} berhasil diselesaikan. Peta rute statis dan animasi telah disimpan sebagai file HTML.")
            self.tabControl.select(self.tab3) # Pindah ke tab output
        else:
            self.output_text.insert(tk.END, "Simulasi gagal atau tidak ada rute ditemukan. Periksa koneksi internet dan API Key Anda.\n")
            messagebox.showerror("Simulasi Gagal", "Simulasi tidak dapat diselesaikan. Pastikan API Key valid dan koneksi internet stabil.")


    def open_static_map(self):
        if self.map_filepath_static and os.path.exists(self.map_filepath_static):
            webbrowser.open(self.map_filepath_static)
            self.tabControl.select(self.tab2) # Pindah ke tab peta
        else:
            messagebox.showerror("Error", "File peta statis tidak ditemukan. Jalankan simulasi terlebih dahulu.")

    def open_animated_map(self):
        if self.map_filepath_animated and os.path.exists(self.map_filepath_animated):
            webbrowser.open(self.map_filepath_animated)
            self.tabControl.select(self.tab2) # Pindah ke tab peta
        else:
            messagebox.showerror("Error", "File peta animasi tidak ditemukan. Jalankan simulasi terlebih dahulu.")

if __name__ == "__main__":
    app = SimulasiApp()
    app.mainloop()