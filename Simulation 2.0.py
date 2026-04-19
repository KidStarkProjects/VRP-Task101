import os
import json
import random
import time
import requests
import math
from typing import List, Dict, Tuple
import plotly.graph_objects as go
import plotly.express as px
import pandas as pd
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
import webbrowser

# ==== Konstanta Global ====
# !!! GANTI DENGAN API KEY TOMTOM YANG VALID !!!
API_KEY = "RnJCaznKckvWSLQct8JJ8ee2HayDhQwS" # Pastikan ini adalah API Key Anda yang valid
TARIF_BBM = 13000  # Rp/liter
GAJI_SOPIR_PER_JAM = 30000  # Rp
BIAYA_PEMELIHARAAN_PER_TRIP = 100000  # Rp
ITERASI_DEFAULT = 3
ANIMATION_TIME_STEP_MIN = 5

HOME_DIR = os.path.expanduser("~")
DOCUMENTS_DIR = os.path.join(HOME_DIR, "Documents")
SAVE_DIRECTORY_BASE = DOCUMENTS_DIR

SAVE_FOLDER_NAME = "simulasi_maps"
FULL_SAVE_DIRECTORY = os.path.join(SAVE_DIRECTORY_BASE, SAVE_FOLDER_NAME)


# ==== Koordinat Kota (Diperbarui) ====
KOTA_KOORDINAT = {
    "Jakarta": (-6.200000, 106.816666),
    "Bandung": (-6.914864, 107.608238),
    "Bogor": (-6.595038, 106.799794) # Koordinat Bogor
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
    return distance

# ==== Fungsi API TomTom ====
def get_routing_data(from_coord: Tuple[float, float], to_coord: Tuple[float, float], avoid_traffic: bool = True, max_alternatives: int = 1) -> Dict:
    if API_KEY == "YOUR_TOMTOM_API_KEY_HERE":
        messagebox.showerror("Error", "Mohon ganti 'YOUR_TOMTOM_API_KEY_HERE' dengan API Key TomTom Anda yang valid.")
        return {}

    url = f"https://api.tomtom.com/routing/1/calculateRoute/{from_coord[0]},{from_coord[1]}:{to_coord[0]},{to_coord[1]}/json"
    params = {
        "key": API_KEY,
        "traffic": "true" if avoid_traffic else "false",
        "travelMode": "truck",
        "routeType": "fastest",
        "computeBestOrder": "false",
        "maxAlternatives": max_alternatives # Tambahkan parameter maxAlternatives
    }
    try:
        response = requests.get(url, params=params)
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        messagebox.showerror("Error API", f"Gagal mengambil rute dari TomTom API: {e}. Periksa koneksi internet dan API Key Anda.")
        return {}

# ==== Fungsi Simulasi Pengiriman ====
def simulate_trip(route: Dict) -> Dict:
    summary = route["summary"]
    travel_time_sec = summary["travelTimeInSeconds"]
    travel_time_min = travel_time_sec / 60
    travel_time_hour = travel_time_min / 60
    distance_km = summary["lengthInMeters"] / 1000

    # Konsumsi BBM per jam adalah acak untuk variabilitas simulasi
    konsumsi_bbm_per_hour = random.uniform(3, 6) # Liter/jam
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
def save_route_map_html(routes: List[Dict], run_number: int, save_dir: str, filename_prefix="Visualisasi_Statis"):
    os.makedirs(save_dir, exist_ok=True)
    filename = f"{filename_prefix}_{run_number}.html"
    filepath = os.path.join(save_dir, filename)

    try:
        fig = go.Figure()
        colors = ["red", "blue", "green", "orange", "purple", "brown"]

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
        if routes and "legs" in routes[0] and len(routes[0]["legs"]) > 0 and "points" in routes[0]["legs"][0]:
            first_route_points = routes[0]["legs"][0]["points"]
            # Titik Awal adalah titik pertama dari rute pertama
            start_coord = (first_route_points[0]["latitude"], first_route_points[0]["longitude"])
            
            # Titik Akhir adalah titik terakhir dari rute terakhir (untuk skenario gabungan, ini akan menjadi titik asal kembali)
            last_route_points = routes[-1]["legs"][0]["points"]
            end_coord = (last_route_points[-1]["latitude"], last_route_points[-1]["longitude"])

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
            title=f"Visualisasi Rute Simulasi Truk (Statis) - Simulasi Ke-{run_number}",
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
        fig.write_html(filepath)
        return filepath
    except Exception as e:
        print(f"Error saving static map to {filepath}: {e}")
        messagebox.showerror("Save Error", f"Gagal menyimpan peta statis: {e}. Pastikan Anda memiliki izin menulis ke direktori '{save_dir}'.")
        return None

# ==== Fungsi untuk Menyiapkan Data Animasi ====
def prepare_animation_data(routes: List[Dict], time_step_min: int = ANIMATION_TIME_STEP_MIN) -> pd.DataFrame:
    animation_frames = []
    
    for i, route in enumerate(routes):
        route_index = i + 1
        # Pastikan rute memiliki struktur yang diharapkan
        if "legs" not in route or not route["legs"] or "points" not in route["legs"][0]:
            print(f"Peringatan: Rute {route_index} tidak memiliki data 'legs' atau 'points' yang diharapkan untuk animasi.")
            continue

        points = route["legs"][0]["points"]
        total_travel_time_sec = route["summary"]["travelTimeInSeconds"]
        total_travel_time_min = total_travel_time_sec / 60

        cumulative_times = [0]
        # Hitung waktu kumulatif berdasarkan jarak proporsional jika kecepatan seragam
        # Ini adalah penyederhanaan; di dunia nyata kecepatan bisa bervariasi per segmen
        total_route_distance_km = route["summary"]["lengthInMeters"] / 1000
        
        for j in range(1, len(points)):
            dist_segment = calculate_haversine_distance(
                points[j-1]["latitude"], points[j-1]["longitude"],
                points[j]["latitude"], points[j]["longitude"]
            )
            # Proporsi waktu berdasarkan jarak segmen
            time_for_segment = (dist_segment / total_route_distance_km) * total_travel_time_min if total_route_distance_km > 0 else 0
            cumulative_times.append(cumulative_times[-1] + time_for_segment)
        
        # Skalakan ulang cumulative_times agar totalnya sesuai dengan total_travel_time_min
        if cumulative_times and cumulative_times[-1] > 0:
            scale_factor = total_travel_time_min / cumulative_times[-1]
            cumulative_times = [t * scale_factor for t in cumulative_times]
        else:
            cumulative_times = [0] * len(points)


        current_time_frame = 0
        max_frame_time = total_travel_time_min # Gunakan waktu tempuh sebenarnya sebagai batas akhir

        # Tambahkan frame pada interval waktu_step_min
        while current_time_frame <= max_frame_time + time_step_min:
            idx1 = 0
            # Temukan segmen di mana current_time_frame berada
            while idx1 < len(cumulative_times) - 1 and cumulative_times[idx1+1] < current_time_frame:
                idx1 += 1
            
            lat, lon = 0, 0
            if idx1 == len(cumulative_times) - 1: # Jika di atau melewati titik terakhir
                lat = points[-1]["latitude"]
                lon = points[-1]["longitude"]
            else: # Interpolasi posisi
                time_diff = cumulative_times[idx1+1] - cumulative_times[idx1]
                if time_diff > 0:
                    ratio = (current_time_frame - cumulative_times[idx1]) / time_diff
                else: # Jika segmen memiliki durasi 0, gunakan titik awal segmen
                    ratio = 0 

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
        
        # Pastikan titik akhir rute selalu ada di frame terakhirnya
        if total_travel_time_min not in [f['time_min'] for f in animation_frames if f['route_id'] == f"Rute {route_index}"]:
             animation_frames.append({
                'route_id': f"Rute {route_index}",
                'latitude': points[-1]["latitude"],
                'longitude': points[-1]["longitude"],
                'time_min': total_travel_time_min,
                'frame_id': int(total_travel_time_min / time_step_min) # Sesuaikan frame_id
            })

    df = pd.DataFrame(animation_frames)
    # Sesuaikan frame_id agar unik per rute tapi konsisten antar rute pada waktu yang sama
    df['frame_id'] = df.groupby('route_id')['time_min'].rank(method='dense', ascending=True).astype(int) - 1
    # Untuk memastikan semua rute muncul di setiap frame yang relevan
    # Jika ada frame_id yang tidak memiliki data untuk rute tertentu, itu akan hilang
    # Ini memerlukan post-processing jika ingin semua rute muncul di setiap frame secara konstan
    df = df.sort_values(by=['frame_id', 'route_id']).reset_index(drop=True)
    return df


# ==== Fungsi untuk Menyimpan Peta Animasi HTML ====
def save_animated_map_html(
    animation_df: pd.DataFrame,
    routes: List[Dict],
    run_number: int,
    save_dir: str,
    filename_prefix="Visualisasi_Animasi"
):
    os.makedirs(save_dir, exist_ok=True)
    filename = f"{filename_prefix}_{run_number}.html"
    filepath = os.path.join(save_dir, filename)

    try:
        fig = go.Figure()
        colors = ["red", "blue", "green", "orange", "purple", "brown"]

        # Gambar semua rute sebagai jalur dasar (putus-putus)
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
                    line=dict(width=2, color=colors[i % len(colors)], dash='dot'),
                    name=f"Rute {i+1} (Dasar)",
                    opacity=0.7,
                    showlegend=True
                ))

        # Tambahkan titik awal dan akhir
        if routes and "legs" in routes[0] and len(routes[0]["legs"]) > 0 and "points" in routes[0]["legs"][0]:
            first_route_points = routes[0]["legs"][0]["points"]
            start_coord = (first_route_points[0]["latitude"], first_route_points[0]["longitude"])
            last_route_points = routes[-1]["legs"][0]["points"] # Untuk skenario gabungan, titik akhir adalah kembali ke asal
            end_coord = (last_route_points[-1]["latitude"], last_route_points[-1]["longitude"])

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

        if not animation_df.empty:
            # Buat animated scatter plot menggunakan px
            animated_scatter_fig = px.scatter_geo(
                animation_df,
                lat="latitude",
                lon="longitude",
                animation_frame="frame_id",
                animation_group="route_id",
                color="route_id",
                size_max=10,
                opacity=1.0,
                symbol="route_id",
                hover_name="route_id",
                hover_data={"time_min": ":.0f", "latitude": False, "longitude": False},
                projection="equirectangular",
                scope='asia',
                title=f"Animasi Perjalanan Truk per Iterasi - Simulasi Ke-{run_number}",
            )
            
            # Tambahkan frames dan data dari px.scatter_geo ke fig utama
            fig.frames = animated_scatter_fig.frames
            # Tambahkan trace animasi, pastikan warnanya konsisten
            for i, trace in enumerate(animated_scatter_fig.data):
                trace.line = dict(color=colors[i % len(colors)]) # Atur warna untuk titik animasi
                fig.add_trace(trace)


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
            lataxis_range = [-10, 0]
            lonaxis_range = [100, 115]


        fig.update_layout(
            title=f"Animasi Perjalanan Truk per Iterasi - Simulasi Ke-{run_number}", # Judul dipindahkan ke layout utama
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
                         label=f"Waktu: {int(animation_df[animation_df['frame_id'] == int(f.name)]['time_min'].iloc[0]) if not animation_df[animation_df['frame_id'] == int(f.name)].empty else 'End'} min")
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
        
        fig.write_html(filepath, auto_play=False)
        return filepath
    except Exception as e:
        print(f"Error saving animated map to {filepath}: {e}")
        messagebox.showerror("Save Error", f"Gagal menyimpan peta animasi: {e}. Pastikan Anda memiliki izin menulis ke direktori '{save_dir}'.")
        return None

# ==== Algoritma Skenario 2: Penilaian Rute Alternatif ====
def evaluate_and_select_best_route(routes: List[Dict]) -> Dict:
    best_route = None
    min_score = float('inf')

    # Bobot untuk kriteria (sesuaikan sesuai prioritas Anda)
    # Anda mungkin perlu menormalisasi nilai-nilai ini jika skalanya sangat berbeda
    # Misalnya, biaya_total bisa sangat besar dibandingkan waktu_tempuh
    W_time = 0.4 # Prioritas waktu
    W_distance = 0.3 # Prioritas jarak
    W_cost = 0.3 # Prioritas biaya

    for route in routes:
        sim_result = simulate_trip(route)
        travel_time_min = sim_result['travel_time_min']
        distance_km = sim_result['distance_km']
        biaya_total = sim_result['biaya_total']

        # Contoh sederhana penskalaan biaya agar tidak mendominasi skor
        # Asumsi biaya_total bisa jutaan, bagi dengan 100000 untuk skala
        scaled_cost = biaya_total / 100000 
        
        score = (W_time * travel_time_min) + \
                (W_distance * distance_km) + \
                (W_cost * scaled_cost)

        if score < min_score:
            min_score = score
            best_route = route
            
    return best_route

# ==== Algoritma Skenario 3: Penggabungan Rute Multi-Tujuan (Greedy) ====
def get_combined_route_data(origin_city: str, destination_cities: List[str], avoid_traffic: bool = True) -> Dict:
    origin_coord = KOTA_KOORDINAT[origin_city]
    
    # Pastikan semua kota tujuan ada dalam KOTA_KOORDINAT
    try:
        unvisited_dest_coords = [KOTA_KOORDINAT[city] for city in destination_cities]
    except KeyError as e:
        messagebox.showerror("Error Destinasi", f"Kota tujuan '{e}' tidak ditemukan dalam daftar kota.")
        return {}
    
    current_location = origin_coord
    
    total_combined_travel_time_sec = 0
    total_combined_distance_m = 0

    # Struktur untuk menyimpan rute gabungan agar bisa divisualisasikan
    full_route_for_animation = {
        "summary": {"travelTimeInSeconds": 0, "lengthInMeters": 0},
        "legs": [{"points": []}]
    }
    
    # Tambahkan titik awal ke rute animasi
    full_route_for_animation["legs"][0]["points"].append({"latitude": origin_coord[0], "longitude": origin_coord[1]})

    while unvisited_dest_coords:
        best_next_destination_coord = None
        min_segment_time_sec = float('inf')
        best_segment_route = None

        for dest_coord in unvisited_dest_coords:
            # Panggil TomTom API untuk setiap segmen
            routing_data = get_routing_data(current_location, dest_coord, avoid_traffic=avoid_traffic)
            if routing_data and "routes" in routing_data:
                # Ambil rute tercepat (biasanya yang pertama)
                segment_route = routing_data["routes"][0]
                segment_time_sec = segment_route["summary"]["travelTimeInSeconds"]
                if segment_time_sec < min_segment_time_sec:
                    min_segment_time_sec = segment_time_sec
                    best_next_destination_coord = dest_coord
                    best_segment_route = segment_route
        
        if best_next_destination_coord:
            # Tambahkan statistik segmen ke total gabungan
            total_combined_travel_time_sec += best_segment_route["summary"]["travelTimeInSeconds"]
            total_combined_distance_m += best_segment_route["summary"]["lengthInMeters"]
            
            # Tambahkan poin dari segmen ini ke rute animasi penuh
            # Lewati titik awal segmen karena sudah ada dari segmen sebelumnya atau awal
            for point in best_segment_route["legs"][0]["points"][1:]:
                full_route_for_animation["legs"][0]["points"].append(point)

            current_location = best_next_destination_coord
            unvisited_dest_coords.remove(best_next_destination_coord)
        else:
            messagebox.showwarning("Penggabungan Rute", "Tidak dapat menemukan rute ke destinasi berikutnya. Menghentikan penggabungan.")
            break # Tidak dapat melanjutkan, keluar dari loop

    # Kembali ke titik asal setelah semua destinasi dikunjungi
    if current_location != origin_coord:
        routing_data_back_to_origin = get_routing_data(current_location, origin_coord, avoid_traffic=avoid_traffic)
        if routing_data_back_to_origin and "routes" in routing_data_back_to_origin:
            return_route = routing_data_back_to_origin["routes"][0]
            total_combined_travel_time_sec += return_route["summary"]["travelTimeInSeconds"]
            total_combined_distance_m += return_route["summary"]["lengthInMeters"]
            
            # Tambahkan poin dari rute kembali ke asal
            for point in return_route["legs"][0]["points"][1:]:
                full_route_for_animation["legs"][0]["points"].append(point)
        else:
            messagebox.showwarning("Penggabungan Rute", "Tidak dapat menemukan rute kembali ke asal. Data mungkin tidak lengkap.")


    # Perbarui summary rute gabungan
    full_route_for_animation["summary"]["travelTimeInSeconds"] = total_combined_travel_time_sec
    full_route_for_animation["summary"]["lengthInMeters"] = total_combined_distance_m
    
    return full_route_for_animation

# ==== Fungsi Utama Simulasi ====
def jalankan_simulasi(scenario_id: int, iterasi: int = ITERASI_DEFAULT, avoid_traffic: bool = True, run_number: int = 1):
    from_city = "Jakarta"
    from_coord = KOTA_KOORDINAT[from_city]
    
    routes_to_simulate_for_output = [] # Daftar rute yang akan disimulasikan dan hasilnya ditampilkan
    routes_for_map_visualization = [] # Daftar rute yang akan digunakan untuk visualisasi peta (bisa berbeda dari routes_to_simulate_for_output)

    if scenario_id == 3: # Skenario Pengiriman Gabungan (Jakarta ke Bandung & Bogor)
        destination_cities = ["Bandung", "Bogor"]
        combined_route = get_combined_route_data(from_city, destination_cities, avoid_traffic=avoid_traffic)
        if combined_route and combined_route["legs"][0]["points"]: # Pastikan rute tidak kosong
            routes_to_simulate_for_output = [combined_route]
            routes_for_map_visualization = [combined_route] # Gunakan rute gabungan untuk peta
        else:
            messagebox.showerror("Simulasi Gagal", "Gagal membuat rute pengiriman gabungan. Periksa API Key dan koneksi.")
            return [], None, None
            
    else: # Skenario 0, 1, 2, 4 (dasar, atau dengan sedikit modifikasi)
        to_city = "Bandung" # Default tujuan untuk skenario non-gabungan
        to_coord = KOTA_KOORDINAT[to_city]
        
        if scenario_id == 2: # Skenario Rute Dinamis Real-Time
            # Minta beberapa alternatif rute dari TomTom
            data_routing = get_routing_data(from_coord, to_coord, avoid_traffic=avoid_traffic, max_alternatives=3) 
            if not data_routing or "routes" not in data_routing:
                return [], None, None
            
            all_alternatives = data_routing["routes"]
            if not all_alternatives:
                messagebox.showwarning("Simulasi", "Tidak ada rute alternatif ditemukan oleh TomTom API.")
                return [], None, None

            best_route = evaluate_and_select_best_route(all_alternatives)
            if best_route:
                routes_to_simulate_for_output = [best_route] # Hanya simulasikan rute terbaik yang dipilih
                routes_for_map_visualization = all_alternatives # Tampilkan semua alternatif di peta (opsional, bisa juga hanya best_route)
            else:
                messagebox.showerror("Simulasi Gagal", "Gagal memilih rute terbaik dari alternatif.")
                return [], None, None
        elif scenario_id == 4: # Skenario Penambahan Truk & Peningkatan Infrastruktur (Simulasi dasar)
            # Untuk skenario 4, ini masih simulasi dasar per rute.
            # Implementasi VRP multi-truk dan pengaruh infrastruktur yang sebenarnya akan lebih kompleks.
            # Untuk tujuan demonstrasi, ini akan menjalankan simulasi rute dasar ke Bandung
            # namun dengan pesan peringatan bahwa implementasi penuh belum ada.
            data_routing = get_routing_data(from_coord, to_coord, avoid_traffic=avoid_traffic, max_alternatives=ITERASI_DEFAULT)
            if not data_routing or "routes" not in data_routing:
                return [], None, None
            routes_to_simulate_for_output = data_routing["routes"][:iterasi]
            routes_for_map_visualization = data_routing["routes"][:iterasi]
        else: # Skenario 0 (Umum) dan 1 (Statis)
            data_routing = get_routing_data(from_coord, to_coord, avoid_traffic=avoid_traffic, max_alternatives=ITERASI_DEFAULT)
            if not data_routing or "routes" not in data_routing:
                return [], None, None
            routes_to_simulate_for_output = data_routing["routes"][:iterasi]
            routes_for_map_visualization = data_routing["routes"][:iterasi]


    hasil_simulasi = []
    # Jalankan simulasi untuk rute yang dipilih untuk output
    for idx, route in enumerate(routes_to_simulate_for_output):
        hasil = simulate_trip(route)
        hasil["route_index"] = idx + 1
        hasil_simulasi.append(hasil)
            
    # Simpan peta statis dan animasi menggunakan routes_for_map_visualization
    map_file_static = save_route_map_html(routes_for_map_visualization, run_number, FULL_SAVE_DIRECTORY)
    animation_df = prepare_animation_data(routes_for_map_visualization)
    map_file_animated = save_animated_map_html(animation_df, routes_for_map_visualization, run_number, FULL_SAVE_DIRECTORY)

    return hasil_simulasi, map_file_static, map_file_animated

# ==== GUI Lokal Tkinter ====
class SimulasiApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Simulasi Sistem Transportasi Truk Nasional")
        self.geometry("900x700") # Sesuaikan ukuran window
        self.resizable(False, False)
        self.map_filepath_static = ""
        self.map_filepath_animated = ""
        self.simulation_run_counter = 0 # Counter for simulation runs
        self.create_widgets()

    def create_widgets(self):
        self.tabControl = ttk.Notebook(self)

        # Tab Kontrol Simulasi
        self.tab1 = ttk.Frame(self.tabControl)
        self.tabControl.add(self.tab1, text='Kontrol Simulasi')

        sim_frame = ttk.LabelFrame(self.tab1, text="Pengaturan Simulasi")
        sim_frame.pack(pady=10, padx=10, fill="x")

        ttk.Label(sim_frame, text="Jumlah Iterasi Rute (default: 3):", font=('Arial', 10, 'bold')).pack(pady=5)
        self.iterasi_entry = ttk.Entry(sim_frame, width=15)
        self.iterasi_entry.insert(0, str(ITERASI_DEFAULT))
        self.iterasi_entry.pack(pady=5)

        self.run_button = ttk.Button(sim_frame, text="Mulai Simulasi Umum", command=lambda: self.run_scenario(0))
        self.run_button.pack(pady=10)

        map_frame = ttk.LabelFrame(self.tab1, text="Visualisasi Peta")
        map_frame.pack(pady=10, padx=10, fill="x")

        self.show_map_button_static = ttk.Button(map_frame, text="Tampilkan Peta Rute (Statis)", command=self.open_static_map, state=tk.DISABLED)
        self.show_map_button_static.pack(pady=5)

        self.show_map_button_animated = ttk.Button(map_frame, text="Tampilkan Animasi Peta Truk", command=self.open_animated_map, state=tk.DISABLED)
        self.show_map_button_animated.pack(pady=5)

        scenario_frame = ttk.LabelFrame(self.tab1, text="Jalankan Skenario Simulasi Khusus")
        scenario_frame.pack(pady=10, padx=10, fill="x")

        ttk.Button(scenario_frame, text="Jalankan Skenario 1 (Rute Tetap & Statis)", command=lambda: self.run_scenario(1)).pack(pady=3)
        ttk.Button(scenario_frame, text="Jalankan Skenario 2 (Rute Dinamis Real-Time)", command=lambda: self.run_scenario(2)).pack(pady=3)
        ttk.Button(scenario_frame, text="Jalankan Skenario 3 (Pengiriman Gabungan)", command=lambda: self.run_scenario(3)).pack(pady=3)
        ttk.Button(scenario_frame, text="Jalankan Skenario 4 (Penambahan Truk - Dasar)", command=lambda: self.run_scenario(4)).pack(pady=3)
        
        # Tab Visualisasi Peta
        self.tab2 = ttk.Frame(self.tabControl)
        self.tabControl.add(self.tab2, text='Visualisasi Peta')
        ttk.Label(self.tab2, text="Peta akan dibuka di browser default Anda setelah simulasi selesai.", font=('Arial', 10)).pack(pady=50)


        # Tab Output Simulasi
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
        avoid_traffic = True # Default untuk kebanyakan skenario

        if scenario_id == 0:
            scenario_name = "Simulasi Umum"
        elif scenario_id == 1:
            scenario_name = "Skenario 1: Rute Tetap & Penjadwalan Statis"
            avoid_traffic = False # Jangan mempertimbangkan lalu lintas
            messagebox.showinfo("Informasi Skenario", "Skenario 1 akan menggunakan rute statis (tidak mempertimbangkan lalu lintas real-time) dan simulasi waktu/biaya standar.")
        elif scenario_id == 2:
            scenario_name = "Skenario 2: Rute Dinamis dengan Sistem Pemantauan Real-Time (Prioritas Waktu, Jarak, Biaya)"
            avoid_traffic = True # Penting untuk mendapatkan data lalu lintas
            messagebox.showinfo("Informasi Skenario", "Skenario 2 akan menggunakan rute dinamis (mempertimbangkan lalu lintas real-time) dan memilih rute terbaik dari alternatif yang ada.")
        elif scenario_id == 3:
            scenario_name = "Skenario 3: Strategi Pengiriman Gabungan (Jakarta ke Bandung & Bogor)"
            avoid_traffic = True # Tetap pertimbangkan lalu lintas untuk rute gabungan
            messagebox.showinfo("Informasi Skenario", "Skenario 3 akan menggabungkan pengiriman dari Jakarta ke Bandung dan Bogor dalam satu rute yang dioptimalkan.")
        elif scenario_id == 4:
            scenario_name = "Skenario 4: Penambahan Truk & Peningkatan Infrastruktur (Simulasi Dasar)"
            avoid_traffic = True
            messagebox.showwarning("Fitur Belum Penuh", "Skenario 4 (Simulasi Armada) memerlukan kerangka simulasi yang lebih canggih. Saat ini hanya menjalankan simulasi rute dasar untuk perbandingan.")
        
        self.simulation_run_counter += 1
        current_run_number = self.simulation_run_counter

        self.output_text.insert(tk.END, f"Menjalankan {scenario_name} (Simulasi ke-{current_run_number})...\n\n")
        self.output_text.update_idletasks()

        hasil, map_file_static, map_file_animated = jalankan_simulasi(scenario_id, iterasi, avoid_traffic=avoid_traffic, run_number=current_run_number)

        if hasil:
            self.map_filepath_static = map_file_static if map_file_static else ""
            self.map_filepath_animated = map_file_animated if map_file_animated else ""

            if self.map_filepath_static:
                self.show_map_button_static.config(state=tk.NORMAL)
            else:
                self.show_map_button_static.config(state=tk.DISABLED)

            if self.map_filepath_animated:
                self.show_map_button_animated.config(state=tk.NORMAL)
            else:
                self.show_map_button_animated.config(state=tk.DISABLED)
            
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

            # Find and display best routes (relevan untuk skenario yang menghasilkan banyak rute)
            if scenario_id in [0, 1]: # Hanya relevan untuk skenario umum atau statis dengan banyak iterasi
                self.output_text.insert(tk.END, "\n--- Rute Terpilih (dari Iterasi) ---\n")

                min_distance = min(d['distance_km'] for d in hasil)
                shortest_routes = [d for d in hasil if d['distance_km'] == min_distance]
                self.output_text.insert(tk.END, f"Rute Terpendek ({min_distance:.2f} km):\n")
                for sr in shortest_routes:
                    self.output_text.insert(tk.END, f"  Rute {sr['route_index']} (Waktu: {sr['travel_time_min']:.2f} menit, Biaya: Rp{sr['biaya_total']:.0f})\n")

                min_time = min(d['travel_time_min'] for d in hasil)
                fastest_routes = [d for d in hasil if d['travel_time_min'] == min_time]
                self.output_text.insert(tk.END, f"Rute Tersingkat ({min_time:.2f} menit):\n")
                for fr in fastest_routes:
                    self.output_text.insert(tk.END, f"  Rute {fr['route_index']} (Jarak: {fr['distance_km']:.2f} km, Biaya: Rp{fr['biaya_total']:.0f})\n")

                min_cost = min(d['biaya_total'] for d in hasil)
                cheapest_routes = [d for d in hasil if d['biaya_total'] == min_cost]
                self.output_text.insert(tk.END, f"Rute Biaya Terendah (Rp{min_cost:.0f}):\n")
                for cr in cheapest_routes:
                    self.output_text.insert(tk.END, f"  Rute {cr['route_index']} (Jarak: {cr['distance_km']:.2f} km, Waktu: {cr['travel_time_min']:.2f} menit)\n")
            elif scenario_id == 2:
                 self.output_text.insert(tk.END, "\n--- Rute Terbaik Dipilih (Skenario 2) ---\n")
                 self.output_text.insert(tk.END, "Rute yang ditampilkan di atas adalah yang terbaik berdasarkan kriteria waktu, jarak, dan biaya.\n")
            elif scenario_id == 3:
                 self.output_text.insert(tk.END, "\n--- Rute Gabungan Terpilih (Skenario 3) ---\n")
                 self.output_text.insert(tk.END, "Rute yang ditampilkan di atas adalah rute tunggal yang menggabungkan beberapa destinasi.\n")


            messagebox.showinfo("Simulasi Selesai", f"{scenario_name} berhasil diselesaikan. Peta rute statis dan animasi telah disimpan di folder:\n{FULL_SAVE_DIRECTORY}")
            self.tabControl.select(self.tab3)
        else:
            self.output_text.insert(tk.END, "Simulasi gagal atau tidak ada rute ditemukan. Periksa koneksi internet dan API Key Anda.\n")
            messagebox.showerror("Simulasi Gagal", "Simulasi tidak dapat diselesaikan. Pastikan API Key valid dan koneksi internet stabil.")


    def open_static_map(self):
        if self.map_filepath_static and os.path.exists(self.map_filepath_static):
            webbrowser.open(self.map_filepath_static)
            self.tabControl.select(self.tab2)
        else:
            messagebox.showerror("Error", f"File peta statis tidak ditemukan di {FULL_SAVE_DIRECTORY}. Jalankan simulasi terlebih dahulu.")

    def open_animated_map(self):
        if self.map_filepath_animated and os.path.exists(self.map_filepath_animated):
            webbrowser.open(self.map_filepath_animated)
            self.tabControl.select(self.tab2)
        else:
            messagebox.showerror("Error", f"File peta animasi tidak ditemukan di {FULL_SAVE_DIRECTORY}. Jalankan simulasi terlebih dahulu.")

if __name__ == "__main__":
    app = SimulasiApp()
    app.mainloop()