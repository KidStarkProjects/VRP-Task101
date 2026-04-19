# SIMULASI LOGISTIK
import os
import random
import requests
import math
import json
import re
import traceback
import threading
from typing import List, Dict, Tuple, Optional
from collections import defaultdict

import plotly.graph_objects as go
import plotly.express as px
import pandas as pd
import numpy as np
import tkinter as tk
from tkinter import ttk, font as tkFont
from tkinter import messagebox
import webbrowser

# ==== Konstanta Global ====
API_KEY_MAPBOX = "ISI TOKEN DISINI" #Pastikan Token Valid Terlebih Dahulu
TARIF_BBM = 13000
GAJI_SOPIR_PER_JAM = 30000
BIAYA_PEMELIHARAAN_PER_TRIP = 100000

JUMLAH_TRUK_DEFAULT = 3
JUMLAH_PENGIRIMAN_DEFAULT = 4
ANIMATION_TIME_STEP_MIN = 60

LAMBDA_JUMLAH_BARANG = 10
MU_WAKTU_PENGAMBILAN_BARANG = 15
SIGMA_WAKTU_PENGAMBILAN_BARANG = 5
MU_SLA_PENGIRIMAN = 240
SIGMA_SLA_PENGIRIMAN = 30
MIN_KONSUMSI_BBM_UNIFORM = 3
MAX_KONSUMSI_BBM_UNIFORM = 6
WAKTU_TEMPUH_INTERNAL_MIN_MENIT = 30
WAKTU_TEMPUH_INTERNAL_MODE_MENIT = 60
WAKTU_TEMPUH_INTERNAL_MAX_MENIT = 120
HOME_DIR = os.path.expanduser("~")
DOCUMENTS_DIR = os.path.join(HOME_DIR, "Documents")
SAVE_DIRECTORY_BASE = DOCUMENTS_DIR
SAVE_FOLDER_NAME = "simulasi_maps_logistik_final"
FULL_SAVE_DIRECTORY = os.path.join(SAVE_DIRECTORY_BASE, SAVE_FOLDER_NAME)
os.makedirs(FULL_SAVE_DIRECTORY, exist_ok=True)

# ==== Koordinat dan Wilayah Kota ====
KOTA_KOORDINAT = {
    "Jakarta": (-6.200000, 106.816666, "Jawa"), "Bandung": (-6.914864, 107.608238, "Jawa"),
    "Surabaya": (-7.257472, 112.752088, "Jawa"), "Semarang": (-6.966667, 110.416664, "Jawa"),
    "Yogyakarta": (-7.795580, 110.369490, "Jawa"), "Medan": (3.595196, 98.672226, "Sumatra"),
    "Palembang": (-2.976074, 104.775429, "Sumatra"), "Makassar": (-5.147665, 119.432732, "Sulawesi"),
    "Denpasar": (-8.670458, 115.212629, "Bali"), "Pekanbaru": (0.507068, 101.447777, "Sumatra"),
    "Padang": (-0.947083, 100.350601, "Sumatra"), "Balikpapan": (-1.237927, 116.852852, "Kalimantan"),
    "Manado": (1.474830, 124.842079, "Sulawesi"), "Pontianak": (-0.027392, 109.333931, "Kalimantan"),
    "Banjarmasin": (-3.316694, 114.590111, "Kalimantan"), "Kupang": (-10.175000, 123.600000, "Nusa Tenggara")
}
KOTA_LIST_DROPDOWN = ["(Pilih Kota)"] + sorted(list(KOTA_KOORDINAT.keys()))
KOTA_LIST_DROPDOWN_ACAK = ["(Acak)"] + sorted(list(KOTA_KOORDINAT.keys()))

WILAYAH_BOUNDS = {
    "Jawa": {"lat": [-8.9, -5.9], "lon": [105.0, 114.7]},
    "Sumatra": {"lat": [-6.0, 6.0], "lon": [95.0, 106.0]},
    "Indonesia": {"lat": [-11, 6], "lon": [95, 141]}
}


# ==== Kelas Entitas Simulasi ====
class Pengiriman:
    id_counter = 0
    def __init__(self, kota_asal: str, kota_tujuan: str, waktu_permintaan_dibuat: float, id_pengiriman:str = None):
        if id_pengiriman is None: Pengiriman.id_counter += 1; self.id_pengiriman = f"P{Pengiriman.id_counter:04d}"
        else: self.id_pengiriman = id_pengiriman
        if kota_asal not in KOTA_KOORDINAT or kota_tujuan not in KOTA_KOORDINAT: raise ValueError(f"Kota asal ({kota_asal}) atau tujuan ({kota_tujuan}) tidak valid.")
        self.kota_asal, self.kota_tujuan = kota_asal, kota_tujuan
        self.jumlah_barang_ton = max(1, np.random.poisson(lam=LAMBDA_JUMLAH_BARANG))
        self.waktu_permintaan_dibuat = waktu_permintaan_dibuat
        self.target_waktu_penyelesaian_sla_menit = max(1, np.random.normal(loc=MU_SLA_PENGIRIMAN, scale=SIGMA_SLA_PENGIRIMAN))
        self.deadline_penyelesaian = waktu_permintaan_dibuat + (self.target_waktu_penyelesaian_sla_menit * 60)
        self.status_pengiriman = "menunggu_alokasi_truk"; self.truk_yang_ditugaskan_id: Optional[str] = None
        self.waktu_truk_dialokasikan: float = -1; self.waktu_mulai_muat: float = -1
        self.estimasi_waktu_pengambilan_barang_menit: float = max(1, np.random.normal(loc=MU_WAKTU_PENGAMBILAN_BARANG, scale=SIGMA_WAKTU_PENGAMBILAN_BARANG))
        self.waktu_selesai_muat: float = -1; self.waktu_keberangkatan_dari_asal: float = -1
        self.estimasi_waktu_tempuh_menit: float = -1; self.jarak_tempuh_km: float = -1
        self.rute_json_detail = None; self.waktu_sampai_tujuan: float = -1; self.waktu_mulai_bongkar: float = -1
        self.estimasi_waktu_bongkar_menit: float = self.estimasi_waktu_pengambilan_barang_menit
        self.waktu_selesai_bongkar: float = -1; self.waktu_penyelesaian_aktual: float = -1
        self.biaya_pengiriman_total: float = 0
        self.rute_depot_ke_asal_json_detail: Optional[Dict] = None
        self.urutan_dalam_tur: Optional[int] = None; self.is_pickup_completed: bool = False; self.is_delivery_completed: bool = False
    def __repr__(self): return (f"Pengiriman(ID: {self.id_pengiriman}, {self.kota_asal} ke {self.kota_tujuan}, {self.jumlah_barang_ton} T, Status: {self.status_pengiriman})")

class Truk:
    id_counter = 0
    def __init__(self, kapasitas_angkut_ton: float, lokasi_awal_depot: str, id_truk:str = None):
        if id_truk is None: Truk.id_counter += 1; self.id_truk = f"T{Truk.id_counter:03d}"
        else: self.id_truk = id_truk
        if lokasi_awal_depot not in KOTA_KOORDINAT: raise ValueError(f"Lokasi depot ({lokasi_awal_depot}) tidak valid.")
        self.kapasitas_angkut_ton = kapasitas_angkut_ton; self.lokasi_depot = lokasi_awal_depot
        self.lokasi_sekarang = lokasi_awal_depot; self.koordinat_sekarang = (KOTA_KOORDINAT[lokasi_awal_depot][0], KOTA_KOORDINAT[lokasi_awal_depot][1])
        self.status = "siaga_di_depot"; self.muatan_saat_ini_ton = 0.0
        self.jadwal_tugas_statis: List[Pengiriman] = []; self.indeks_tugas_statis_saat_ini: int = 0
        self.tur_konsolidasi_saat_ini: List[Tuple[Pengiriman, str]] = []; self.indeks_waypoint_tur_saat_ini: int = 0
        self.target_destinasi_berikutnya_nama: Optional[str] = None; self.waktu_event_selanjutnya: float = 0
        self.total_km_operasional = 0.0; self.total_jam_operasional_mengemudi = 0.0
        self.total_jam_operasional_memuat = 0.0; self.total_jam_operasional_membongkar = 0.0
        self.total_biaya_bbm = 0.0; self.total_biaya_sopir = 0.0; self.total_biaya_pemeliharaan = 0.0
        self.jumlah_trip_selesai = 0
        self.pengiriman_saat_ini_id: Optional[str] = None
    def __repr__(self): return (f"Truk(ID: {self.id_truk}, Kap: {self.kapasitas_angkut_ton} T, Lok: {self.lokasi_sekarang}, Status: {self.status}, Muatan: {self.muatan_saat_ini_ton} T, NextEvent: {self.waktu_event_selanjutnya:.2f})")
    def apakah_siaga_untuk_tugas_baru(self, waktu_simulasi: float) -> bool:
        return self.status in ["siaga_di_depot", "siaga_setelah_bongkar", "siaga_setelah_tur"] and self.waktu_event_selanjutnya <= waktu_simulasi
    def bisa_angkut(self, berat_tambahan_ton: float) -> bool:
        return (self.muatan_saat_ini_ton + berat_tambahan_ton) <= self.kapasitas_angkut_ton

# ==== Fungsi Inisialisasi Sistem ====
armada_truk_global: List[Truk] = []
daftar_pengiriman_global: List[Pengiriman] = []
def inisialisasi_sistem_simulasi_global(jumlah_truk: int, kapasitas_truk_default: float = 10, daftar_kota_depot_str: Optional[str] = None):
    global armada_truk_global; armada_truk_global = []; Truk.id_counter = 0; kota_depot_valid = []
    if daftar_kota_depot_str:
        nama_kota_depot = [kota.strip() for kota in daftar_kota_depot_str.split(',') if kota.strip()]
        for nama_kota in nama_kota_depot:
            if nama_kota in KOTA_KOORDINAT: kota_depot_valid.append(nama_kota)
            else: print(f"Peringatan: Kota depot '{nama_kota}' tidak ditemukan, diabaikan.")
    if not kota_depot_valid: kota_depot_valid = list(KOTA_KOORDINAT.keys());
    if not kota_depot_valid: kota_depot_valid = ["Jakarta"]
    for _ in range(jumlah_truk):
        depot = random.choice(kota_depot_valid)
        truk = Truk(kapasitas_angkut_ton=kapasitas_truk_default + random.uniform(-2, 5), lokasi_awal_depot=depot)
        armada_truk_global.append(truk)
    print(f"Inisialisasi {len(armada_truk_global)} truk. Depot di: {', '.join(set(t.lokasi_depot for t in armada_truk_global))}")

def generate_permintaan_pengiriman_global(jumlah_permintaan:int, waktu_simulasi_awal:float=0.0, durasi_generasi_hari:int=1, mode_pengiriman:str="Acak ke Acak", fixed_origin_city:str=None, fixed_destination_city:str=None):
    global daftar_pengiriman_global; daftar_pengiriman_global=[]; Pengiriman.id_counter=0; kota_tersedia=list(KOTA_KOORDINAT.keys())
    if not kota_tersedia: print("Error: Tidak ada kota tersedia."); return
    for _ in range(jumlah_permintaan):
        asal,tujuan=None,None
        if mode_pengiriman=="Satu Asal ke Satu Tujuan":
            if fixed_origin_city and fixed_destination_city and fixed_origin_city!=fixed_destination_city: asal,tujuan=fixed_origin_city,fixed_destination_city
            else: print(f"Peringatan: Mode 'Satu Asal ke Satu Tujuan' perlu Asal & Tujuan beda."); continue
        elif mode_pengiriman=="Satu Asal ke Banyak Tujuan (Acak)":
            if fixed_origin_city:
                asal=fixed_origin_city
                possible_destinations=[k for k in kota_tersedia if k!=asal]
                if possible_destinations:
                    tujuan=random.choice(possible_destinations)
                else:
                    print(f"Peringatan: Tdk ada tujuan acak valid u/ asal '{asal}'."); continue
            else:
                print(f"Peringatan: Mode 'Satu Asal ke Banyak Tujuan' perlu Asal Tetap."); continue
        elif mode_pengiriman=="Banyak Asal (Acak) ke Satu Tujuan":
            if fixed_destination_city:
                tujuan=fixed_destination_city
                possible_origins=[k for k in kota_tersedia if k!=tujuan]
                if possible_origins:
                    asal=random.choice(possible_origins)
                else:
                    print(f"Peringatan: Tdk ada asal acak valid u/ tujuan '{tujuan}'."); continue
            else:
                print(f"Peringatan: Mode 'Banyak Asal ke Satu Tujuan' perlu Tujuan Tetap."); continue
        else: # Default "Acak ke Acak"
            if len(kota_tersedia)<2: print("Peringatan: Mode 'Acak ke Acak' butuh min 2 kota."); continue
            asal,tujuan=random.sample(kota_tersedia,2)
        if not asal or not tujuan: print(f"Peringatan: Gagal tentukan asal/tujuan mode '{mode_pengiriman}'."); continue
        waktu_dibuat=waktu_simulasi_awal+random.uniform(0,durasi_generasi_hari*24*60*60)
        pengiriman=Pengiriman(kota_asal=asal,kota_tujuan=tujuan,waktu_permintaan_dibuat=waktu_dibuat)
        daftar_pengiriman_global.append(pengiriman)
    daftar_pengiriman_global.sort(key=lambda p:p.waktu_permintaan_dibuat)

# ==== Fungsi Helper & API ====
def calculate_haversine_distance(lat1,lon1,lat2,lon2)->float:R=6371;lat1_r,lon1_r,lat2_r,lon2_r=map(math.radians,[lat1,lon1,lat2,lon2]);dlat=lat2_r-lat1_r;dlon=lon2_r-lon1_r;a=math.sin(dlat/2)**2+math.cos(lat1_r)*math.cos(lat2_r)*math.sin(dlon/2)**2;c=2*math.atan2(math.sqrt(a),math.sqrt(1-a));return R*c

def decode_polyline(polyline_str):
    index, lat, lng = 0, 0, 0; coordinates = []; changes = {'latitude': 0, 'longitude': 0}
    while index < len(polyline_str):
        for unit in ['latitude', 'longitude']:
            shift, result = 0, 0
            while True:
                if index >= len(polyline_str): raise ValueError("Invalid polyline string: unexpected end.")
                byte = ord(polyline_str[index]) - 63; index += 1; result |= (byte & 0x1f) << shift; shift += 5;
                if not byte >= 0x20: break
            if result & 1: changes[unit] = ~(result >> 1)
            else: changes[unit] = (result >> 1)
        lat += changes['latitude']; lng += changes['longitude']; coordinates.append({'latitude': lat/1E5, 'longitude': lng/1E5})
    return coordinates

def get_routing_data_from_mapbox_api(from_coord: Tuple[float, float], to_coord: Tuple[float, float], avoid_traffic_realtime: bool = True) -> Optional[Dict]:
    if not API_KEY_MAPBOX or API_KEY_MAPBOX == "MASUKKAN_API_KEY_MAPBOX_ANDA_DI_SINI":
        print("PERINGATAN: API Key Mapbox belum diatur. Silakan masukkan API Key Anda.")
        return None
    coords_str = f"{from_coord[1]},{from_coord[0]};{to_coord[1]},{to_coord[0]}"
    profile = "mapbox/driving-traffic" if avoid_traffic_realtime else "mapbox/driving"
    url = f"https://api.mapbox.com/directions/v5/{profile}/{coords_str}"
    params = {"access_token": API_KEY_MAPBOX, "geometries": "polyline", "overview": "full", "steps": "false", "alternatives": "false"}
    try:
        response = requests.get(url, params=params, timeout=15); response.raise_for_status(); data = response.json()
        if data.get("code") == "Ok" and data.get("routes"):
            route = data["routes"][0]
            if not route.get("geometry"):
                print(f"Error Mapbox API: Rute ditemukan tetapi tidak ada data geometri untuk {from_coord} ke {to_coord}.")
                return None
            distance_meters = route["distance"]; duration_seconds = route["duration"]
            points_decoded = decode_polyline(route["geometry"])
            return {"summary": {"lengthInMeters": distance_meters, "travelTimeInSeconds": duration_seconds, "trafficDelayInSeconds": 0, "noTrafficTravelTimeInSeconds": duration_seconds},
                    "legs": [{"summary": {"lengthInMeters": distance_meters, "travelTimeInSeconds": duration_seconds}, "points": points_decoded}]}
        else:
            print(f"Error Mapbox API: {data.get('code')} - {data.get('message', 'No route found')}"); return None
    except requests.exceptions.Timeout: print("Error API Mapbox: Timeout."); return None
    except requests.exceptions.HTTPError as h: print(f"Error API Mapbox: HTTP {h.response.status_code} - {h.response.text}"); return None
    except requests.exceptions.RequestException as e: print(f"Error API Mapbox: {e}"); return None
    except Exception as ep:
        print(f"Error tidak terduga saat memproses respons Mapbox: {ep}")
        print(traceback.format_exc())
        return None

def estimasi_rute_internal(coord_asal:Tuple[float,float],coord_tujuan:Tuple[float,float])->Dict:
    jarak_km=calculate_haversine_distance(coord_asal[0],coord_asal[1],coord_tujuan[0],coord_tujuan[1])
    waktu_tempuh_menit_internal=np.random.triangular(left=WAKTU_TEMPUH_INTERNAL_MIN_MENIT,mode=WAKTU_TEMPUH_INTERNAL_MODE_MENIT,right=WAKTU_TEMPUH_INTERNAL_MAX_MENIT)
    waktu_tempuh_detik_internal=waktu_tempuh_menit_internal*60
    return {"summary":{"lengthInMeters":jarak_km*1000,"travelTimeInSeconds":waktu_tempuh_detik_internal,"trafficDelayInSeconds":0,"noTrafficTravelTimeInSeconds":waktu_tempuh_detik_internal},"legs":[{"summary":{"lengthInMeters":jarak_km*1000,"travelTimeInSeconds":waktu_tempuh_detik_internal},"points":[{"latitude":coord_asal[0],"longitude":coord_asal[1]},{"latitude":coord_tujuan[0],"longitude":coord_tujuan[1]}]}]}

def get_route_for_segment(kota_asal: str, kota_tujuan: str, routing_mode: str, avoid_traffic: bool, force_internal_on_api_failure: bool = True) -> Optional[Dict]:
    coord_asal = (KOTA_KOORDINAT[kota_asal][0], KOTA_KOORDINAT[kota_asal][1])
    coord_tujuan = (KOTA_KOORDINAT[kota_tujuan][0], KOTA_KOORDINAT[kota_tujuan][1])
    if routing_mode == "Model Rute Internal (Non-API)": return estimasi_rute_internal(coord_asal, coord_tujuan)
    else:
        route_data = get_routing_data_from_mapbox_api(coord_asal, coord_tujuan, avoid_traffic)
        if route_data: return route_data
        elif force_internal_on_api_failure:
            print(f"  PERINGATAN: API Mapbox gagal untuk {kota_asal} ke {kota_tujuan}. Menggunakan fallback Model Rute Internal.")
            return estimasi_rute_internal(coord_asal, coord_tujuan)
        else: return None

# ==== Fungsi Pemrosesan Event & Biaya ====
def proses_event_muat_selesai(truk:Truk,pengiriman:Pengiriman,waktu_event:float):pengiriman.waktu_selesai_muat=waktu_event;pengiriman.is_pickup_completed=True;truk.muatan_saat_ini_ton+=pengiriman.jumlah_barang_ton;truk.total_jam_operasional_memuat+=(pengiriman.estimasi_waktu_pengambilan_barang_menit/60)
def proses_event_bongkar_selesai(truk:Truk,pengiriman:Pengiriman,waktu_event:float):
    pengiriman.waktu_selesai_bongkar=waktu_event;pengiriman.is_delivery_completed=True;pengiriman.waktu_penyelesaian_aktual=waktu_event
    truk.muatan_saat_ini_ton-=pengiriman.jumlah_barang_ton;
    if truk.muatan_saat_ini_ton<0.001:truk.muatan_saat_ini_ton=0.0
    truk.total_jam_operasional_membongkar+=(pengiriman.estimasi_waktu_bongkar_menit/60);pengiriman.status_pengiriman="selesai_terlambat" if waktu_event>pengiriman.deadline_penyelesaian else "selesai"
    pengiriman.biaya_pengiriman_total+=BIAYA_PEMELIHARAAN_PER_TRIP;truk.total_biaya_pemeliharaan+=BIAYA_PEMELIHARAAN_PER_TRIP;truk.jumlah_trip_selesai+=1
def hitung_biaya_segmen_perjalanan(jarak_km:float,waktu_tempuh_jam:float)->Tuple[float,float,float]:konsumsi_bbm_per_hour=random.uniform(MIN_KONSUMSI_BBM_UNIFORM,MAX_KONSUMSI_BBM_UNIFORM);fuel_liters_trip=konsumsi_bbm_per_hour*waktu_tempuh_jam;biaya_bbm_trip=fuel_liters_trip*TARIF_BBM;biaya_sopir_trip=waktu_tempuh_jam*GAJI_SOPIR_PER_JAM;return biaya_bbm_trip,biaya_sopir_trip,fuel_liters_trip
def simulate_actual_trip(pengiriman:Pengiriman,truk:Truk,route_summary:Dict,waktu_mulai_trip_detik:float)->Dict:
    pengiriman.waktu_mulai_muat=waktu_mulai_trip_detik;waktu_muat_detik=pengiriman.estimasi_waktu_pengambilan_barang_menit*60
    pengiriman.waktu_selesai_muat=pengiriman.waktu_mulai_muat+waktu_muat_detik;truk.status="memuat_barang"
    truk.total_jam_operasional_memuat+=waktu_muat_detik/3600;pengiriman.waktu_keberangkatan_dari_asal=pengiriman.waktu_selesai_muat
    travel_time_sec_api=route_summary["travelTimeInSeconds"];pengiriman.estimasi_waktu_tempuh_menit=travel_time_sec_api/60
    pengiriman.jarak_tempuh_km=route_summary["lengthInMeters"]/1000;truk.status="dalam_perjalanan_mengantar"
    truk.lokasi_sekarang=f"Menuju {pengiriman.kota_tujuan}";truk.target_destinasi_berikutnya_nama=pengiriman.kota_tujuan
    truk.total_km_operasional+=pengiriman.jarak_tempuh_km;truk.total_jam_operasional_mengemudi+=travel_time_sec_api/3600
    b_bbm,b_sopir,_=hitung_biaya_segmen_perjalanan(pengiriman.jarak_tempuh_km,travel_time_sec_api/3600)
    pengiriman.biaya_pengiriman_total+=b_bbm+b_sopir;truk.total_biaya_bbm+=b_bbm;truk.total_biaya_sopir+=b_sopir
    pengiriman.waktu_sampai_tujuan=pengiriman.waktu_keberangkatan_dari_asal+travel_time_sec_api
    pengiriman.waktu_mulai_bongkar=pengiriman.waktu_sampai_tujuan;waktu_bongkar_detik=pengiriman.estimasi_waktu_bongkar_menit*60
    pengiriman.waktu_selesai_bongkar=pengiriman.waktu_mulai_bongkar+waktu_bongkar_detik;truk.status="membongkar_barang"
    truk.total_jam_operasional_membongkar+=waktu_bongkar_detik/3600;pengiriman.waktu_penyelesaian_aktual=pengiriman.waktu_selesai_bongkar
    pengiriman.status_pengiriman="selesai";
    if pengiriman.waktu_penyelesaian_aktual > pengiriman.deadline_penyelesaian: pengiriman.status_pengiriman="selesai_terlambat"
    truk.muatan_saat_ini_ton=0; truk.pengiriman_saat_ini_id = None
    truk.lokasi_sekarang=pengiriman.kota_tujuan
    truk.koordinat_sekarang=(KOTA_KOORDINAT[pengiriman.kota_tujuan][0], KOTA_KOORDINAT[pengiriman.kota_tujuan][1])
    truk.waktu_event_selanjutnya=pengiriman.waktu_penyelesaian_aktual;truk.jumlah_trip_selesai+=1
    truk.total_biaya_pemeliharaan+=BIAYA_PEMELIHARAAN_PER_TRIP;pengiriman.biaya_pengiriman_total+=BIAYA_PEMELIHARAAN_PER_TRIP
    return {"id_pengiriman":pengiriman.id_pengiriman,"id_truk":truk.id_truk,"asal":pengiriman.kota_asal,"tujuan":pengiriman.kota_tujuan,
            "jarak_km":pengiriman.jarak_tempuh_km,"waktu_tempuh_aktual_menit":(pengiriman.waktu_sampai_tujuan-pengiriman.waktu_keberangkatan_dari_asal)/60,
            "waktu_muat_menit":waktu_muat_detik/60,"waktu_bongkar_menit":waktu_bongkar_detik/60,
            "total_waktu_siklus_pengiriman_menit":(pengiriman.waktu_penyelesaian_aktual-pengiriman.waktu_mulai_muat)/60 if pengiriman.waktu_mulai_muat > 0 else -1,
            "status_akhir_pengiriman":pengiriman.status_pengiriman,"biaya_total_trip":pengiriman.biaya_pengiriman_total,
            "waktu_permintaan_dibuat_jam":pengiriman.waktu_permintaan_dibuat/3600,
            "waktu_selesai_aktual_jam":pengiriman.waktu_penyelesaian_aktual/3600 if pengiriman.waktu_penyelesaian_aktual > 0 else -1,
            "deadline_sla_jam":pengiriman.deadline_penyelesaian/3600}

# ==== Fungsi Visualisasi Peta ====
def _get_status_display_dan_warna(status_str: str) -> Tuple[str, str, str]:
    """Helper untuk mendapatkan teks tampilan, warna, dan kelas CSS berdasarkan status."""
    if status_str == "selesai":
        return "Tepat Waktu", "#2ca02c", "log-ontime"
    elif status_str == "selesai_terlambat":
        return "Terlambat", "#ff7f0e", "log-late"
    else:
        # Menangani semua status gagal & tidak terproses
        display_text = status_str.replace('_', ' ').title()
        return display_text, "#d62728", "log-failed"
# FUNGSI BARU DENGAN LOGIKA WAKTU YANG DISEMPURNAKAN
def _prepare_animation_events(pengiriman_diproses_final: List[Pengiriman]) -> defaultdict:
    """
    Helper untuk mempersiapkan event log untuk peta dinamis.
    PERBAIKAN: Menggunakan waktu permintaan dibuat untuk log pengiriman yang gagal.
    """
    animation_events = defaultdict(list)
    for p in pengiriman_diproses_final:
        
        # Logika Penentuan Frame untuk Log ---
        event_time_seconds = 0
        # Prioritas 1: Gunakan waktu penyelesaian aktual jika ada (untuk pengiriman sukses).
        if p.waktu_penyelesaian_aktual > 0:
            event_time_seconds = p.waktu_penyelesaian_aktual
        # Prioritas 2: Jika gagal, gunakan waktu permintaan dibuat agar log muncul sesuai timeline.
        elif p.status_pengiriman != "menunggu_alokasi_truk":
            event_time_seconds = p.waktu_permintaan_dibuat
        
        # Hitung frame_id berdasarkan waktu event yang relevan
        frame_id = int(round((event_time_seconds / 60) / ANIMATION_TIME_STEP_MIN))

        status_text, status_color_hex, status_css_class = _get_status_display_dan_warna(p.status_pengiriman)
        msg = f"<b>{p.id_pengiriman}:</b> "
        if p.status_pengiriman.startswith("selesai"):
            msg += f"{p.kota_asal} → {p.kota_tujuan} <span style='color:{status_color_hex}; font-weight:bold;'>({status_text})</span>"
        else:
            msg += f"Status <span style='color:{status_color_hex}; font-weight:bold;'>({status_text})</span>"
        animation_events[frame_id].append({"message": msg, "css_class": status_css_class})
    return animation_events
def _configure_animation_layout(fig, max_frame, all_cities_for_map, run_number):
    """Helper untuk mengatur layout peta animasi."""
    # Logika Zoom Peta Dinamis 
    pulau_terlibat = {KOTA_KOORDINAT[kota][2] for kota in all_cities_for_map if kota in KOTA_KOORDINAT}
    if len(pulau_terlibat) == 1:
        pulau = pulau_terlibat.pop()
        bounds = WILAYAH_BOUNDS.get(pulau, WILAYAH_BOUNDS["Indonesia"])
    else:
        bounds = WILAYAH_BOUNDS["Indonesia"]
    
    lataxis_range, lonaxis_range = bounds['lat'], bounds['lon']
    map_center_lat, map_center_lon = sum(lataxis_range) / 2, sum(lonaxis_range) / 2
    
    fig.update_layout(
        title=f"Visualisasi Animasi Pengiriman - Simulasi Ke-{run_number}",
        updatemenus=[dict(
            type="buttons", direction="right", x=0.6, y=1.1,
            buttons=[
                dict(label="Play", method="animate", args=[[None], {"frame": {"duration": 200, "redraw": True}, "fromcurrent": True, "transition": {"duration": 100}}]),
                dict(label="Pause", method="animate", args=[[None], {"frame": {"duration": 0, "redraw": False}, "mode": "immediate"}])
            ]
        )],
        sliders=[dict(
            active=0, currentvalue={"prefix": "Waktu Simulasi: "}, pad={"t": 50},
            steps=[dict(
                label=f"H{int((i*ANIMATION_TIME_STEP_MIN)//(24*60))} {int(((i*ANIMATION_TIME_STEP_MIN)%(24*60))//60):02d}:{int((i*ANIMATION_TIME_STEP_MIN)%60):02d}",
                method="animate",
                args=[[str(i)], {"frame": {"duration": 200, "redraw": False}, "mode": "immediate"}]
            ) for i in range(int(max_frame) + 1)]
        )],
        legend=dict(traceorder='grouped', orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1),
        geo=dict(scope='asia', center=dict(lat=map_center_lat, lon=map_center_lon),
                 lataxis_range=lataxis_range, lonaxis_range=lonaxis_range,
                 projection_type='mercator', showland=True, landcolor="rgb(220, 220, 220)")
    )

def save_route_map_html_multi(processed_shipments_with_obj:List[Pengiriman], run_number:int, save_dir:str, filename_prefix="Visualisasi_Multi_Rute_Statis", depots_to_mark:Optional[List[str]]=None, shipment_summary:Optional[Dict]=None, truck_summary:Optional[Dict]=None):
    os.makedirs(save_dir, exist_ok=True)
    filename = f"{filename_prefix}_{run_number}.html"
    filepath = os.path.join(save_dir, filename)
    fig = go.Figure()
    colors = px.colors.qualitative.Plotly
    
    annotations = []

    if depots_to_mark:
        depot_lats = [KOTA_KOORDINAT[kota][0] for kota in depots_to_mark if kota in KOTA_KOORDINAT]
        depot_lons = [KOTA_KOORDINAT[kota][1] for kota in depots_to_mark if kota in KOTA_KOORDINAT]
        depot_texts = [f"Depot: {kota}" for kota in depots_to_mark if kota in KOTA_KOORDINAT]
        fig.add_trace(go.Scattergeo(
            lon=depot_lons, lat=depot_lats, mode='markers',
            marker=dict(size=12, color='black', symbol='diamond-wide', line=dict(width=1, color='white')),
            name='Lokasi Depot', hoverinfo='text', text=depot_texts
        ))

    actual_routes_to_plot = [p for p in processed_shipments_with_obj if p.status_pengiriman.startswith("selesai")]

    if not actual_routes_to_plot and not depots_to_mark:
        print("Tidak ada rute valid untuk visualisasi statis.")
        return None

    all_lats, all_lons = [], []
    all_cities = set(depots_to_mark if depots_to_mark else [])


    for idx, p_obj in enumerate(actual_routes_to_plot):
        all_cities.add(p_obj.kota_asal)
        all_cities.add(p_obj.kota_tujuan)
        color = colors[idx % len(colors)]
        
        if p_obj.rute_depot_ke_asal_json_detail and "legs" in p_obj.rute_depot_ke_asal_json_detail and p_obj.rute_depot_ke_asal_json_detail["legs"]:
            route_depot_asal = p_obj.rute_depot_ke_asal_json_detail
            if route_depot_asal["legs"][0]["points"]:
                points = route_depot_asal["legs"][0]["points"]
                lats = [pt["latitude"] for pt in points]; lons = [pt["longitude"] for pt in points]
                all_lats.extend(lats); all_lons.extend(lons)
                fig.add_trace(go.Scattergeo(lon=lons, lat=lats, mode='lines', line=dict(width=2, color=color, dash='dash'), showlegend=False, hoverinfo='none'))

        if p_obj.rute_json_detail and "legs" in p_obj.rute_json_detail and p_obj.rute_json_detail["legs"]:
            route_utama = p_obj.rute_json_detail
            if route_utama["legs"][0]["points"]:
                points = route_utama["legs"][0]["points"]
                lats = [pt["latitude"] for pt in points]; lons = [pt["longitude"] for pt in points]
                all_lats.extend(lats); all_lons.extend(lons)
                
                legend_text = f"Truk {p_obj.truk_yang_ditugaskan_id[-3:]} ({p_obj.kota_asal} ke {p_obj.kota_tujuan})"
                fig.add_trace(go.Scattergeo(lon=lons, lat=lats, mode='lines', line=dict(width=3, color=color), name=legend_text, hoverinfo='none', legendgroup=p_obj.id_pengiriman))
                
                fig.add_trace(go.Scattergeo(lon=[lons[0]], lat=[lats[0]], mode='markers', marker=dict(size=10, color=color, symbol='circle'), 
                                            text=f"Asal: {p_obj.kota_asal}", hoverinfo='text', name=f"Asal: {p_obj.kota_asal}", showlegend=False, legendgroup=p_obj.id_pengiriman))
                fig.add_trace(go.Scattergeo(lon=[lons[-1]], lat=[lats[-1]], mode='markers', marker=dict(size=10, color=color, symbol='star'),
                                            text=f"Tujuan: {p_obj.kota_tujuan}", hoverinfo='text', name=f"Tujuan: {p_obj.kota_tujuan}", showlegend=False, legendgroup=p_obj.id_pengiriman))
    
    if shipment_summary and truck_summary:
        summary_text = (f"<b>Rangkuman Simulasi Ke-{run_number}</b><br><br>"
                        f"<b>Pengiriman:</b><br>"
                        f"  - Tepat Waktu: {shipment_summary.get('tepat_waktu', 0)}<br>"
                        f"  - Terlambat: {shipment_summary.get('terlambat', 0)}<br>"
                        f"  - Gagal: {shipment_summary.get('gagal', 0)}<br><br>"
                        f"<b>Armada:</b><br>"
                        f"  - Truk Beroperasi: {truck_summary.get('beroperasi', 0)}<br>"
                        f"  - Truk Menganggur: {truck_summary.get('menganggur', 0)}")

        annotations.append(dict(x=0.01, y=0.99, xref='paper', yref='paper', text=summary_text,
                                showarrow=False, align='left', font=dict(size=12, color='black'),
                                bgcolor='rgba(255, 255, 240, 0.85)', bordercolor='black', borderwidth=1))

    # Logika Zoom Peta Dinamis
    pulau_terlibat = {KOTA_KOORDINAT[kota][2] for kota in all_cities}
    if len(pulau_terlibat) == 1:
        pulau = pulau_terlibat.pop()
        if pulau in WILAYAH_BOUNDS:
            bounds = WILAYAH_BOUNDS[pulau]
            lataxis_range, lonaxis_range = bounds['lat'], bounds['lon']
            map_center_lat = sum(lataxis_range) / 2
            map_center_lon = sum(lonaxis_range) / 2
        else:
            bounds = WILAYAH_BOUNDS["Indonesia"]
            lataxis_range, lonaxis_range = bounds['lat'], bounds['lon']
            map_center_lat, map_center_lon = -2.5489, 118.0149
    else:
        bounds = WILAYAH_BOUNDS["Indonesia"]
        lataxis_range, lonaxis_range = bounds['lat'], bounds['lon']
        map_center_lat, map_center_lon = -2.5489, 118.0149

    fig.update_layout(title=f"Peta Rute Pengiriman Aktual (Statis) - Simulasi Ke-{run_number}",
                      annotations=annotations,
                      geo=dict(scope='asia', projection_type='mercator', 
                               center=dict(lat=map_center_lat, lon=map_center_lon),
                               showland=True, landcolor="rgb(220, 220, 220)", countrycolor="rgb(200, 200, 200)",
                               lataxis_range=lataxis_range, lonaxis_range=lonaxis_range, subunitcolor="grey"),
                      hovermode='closest', legend_title_text='Legenda Pengiriman',
                      legend=dict(orientation="v", yanchor="top", y=1, xanchor="right", x=1.15))
    try:
        fig.write_html(filepath)
        return filepath
    except Exception as e:
        print(f"Error menyimpan peta statis: {e}")
        return None

def _create_animation_frames_for_segment(route_data: Dict, start_time_min: float, time_step_min: int, legend_label: str, hover_text: str) -> List[Dict]:
    segment_frames = []
    if not (route_data and "legs" in route_data and route_data["legs"] and "points" in route_data["legs"][0] and route_data["legs"][0]["points"]):
        return []
        
    points = route_data["legs"][0]["points"]
    total_travel_time_sec = route_data["summary"]["travelTimeInSeconds"]
    if total_travel_time_sec <= 0: return []
    total_travel_time_min = total_travel_time_sec / 60

    cumulative_segment_times_min = [0]
    total_dist_km = route_data["summary"]["lengthInMeters"] / 1000
    if total_dist_km > 0 and len(points) > 1:
        current_dist = 0
        for j in range(1, len(points)):
            dist_seg = calculate_haversine_distance(points[j-1]["latitude"], points[j-1]["longitude"], points[j]["latitude"], points[j]["longitude"])
            current_dist += dist_seg
            time_seg_min = (dist_seg / total_dist_km) * total_travel_time_min
            cumulative_segment_times_min.append(cumulative_segment_times_min[-1] + time_seg_min)
    else:
        cumulative_segment_times_min = np.linspace(0, total_travel_time_min, len(points) if len(points) > 1 else 2).tolist()

    if not cumulative_segment_times_min: return []
    
    if cumulative_segment_times_min[-1] > 0:
        scale_factor = total_travel_time_min / cumulative_segment_times_min[-1]
        cumulative_segment_times_min = [t * scale_factor for t in cumulative_segment_times_min]

    current_relative_time_min = 0
    max_relative_time_min = total_travel_time_min
    
    while True:
        frame_global_time_min = start_time_min + current_relative_time_min
        
        interp_lat, interp_lon = (0, 0)
        if current_relative_time_min >= max_relative_time_min:
             interp_lat, interp_lon = points[-1]["latitude"], points[-1]["longitude"]
        else:
            idx = np.searchsorted(cumulative_segment_times_min, current_relative_time_min, side='right')
            idx = min(idx, len(points) - 1)
            idx0 = max(0, idx - 1)
            
            time_diff_seg = cumulative_segment_times_min[idx] - cumulative_segment_times_min[idx0]
            ratio = (current_relative_time_min - cumulative_segment_times_min[idx0]) / time_diff_seg if time_diff_seg > 0 else 0
            ratio = max(0, min(1, ratio))

            interp_lat = points[idx0]["latitude"] + (points[idx]["latitude"] - points[idx0]["latitude"]) * ratio
            interp_lon = points[idx0]["longitude"] + (points[idx]["longitude"] - points[idx0]["longitude"]) * ratio
        
        segment_frames.append({
            'legend_anim_label': legend_label, 'latitude': interp_lat, 'longitude': interp_lon,
            'time_sim_min': frame_global_time_min, 'hover_text': hover_text
        })

        if current_relative_time_min >= max_relative_time_min: break
        current_relative_time_min += time_step_min
        current_relative_time_min = min(current_relative_time_min, max_relative_time_min)
        
    return segment_frames

def prepare_animation_data_multi(processed_shipments_with_obj:List[Pengiriman], time_step_min:int=ANIMATION_TIME_STEP_MIN)->pd.DataFrame:
    animation_frames = []
    for p_obj in processed_shipments_with_obj:
        if not (p_obj.status_pengiriman.startswith("selesai")): continue
            
        legend_anim_label = f"Truk {p_obj.truk_yang_ditugaskan_id[-3:]}"
        hover_text = f"Truk {p_obj.truk_yang_ditugaskan_id[-3:]}; {p_obj.id_pengiriman}; {p_obj.kota_asal} -> {p_obj.kota_tujuan}"

        if p_obj.rute_depot_ke_asal_json_detail:
            start_time_leg1_min = (p_obj.waktu_truk_dialokasikan) / 60 if p_obj.waktu_truk_dialokasikan > 0 else 0
            frames_leg1 = _create_animation_frames_for_segment(
                p_obj.rute_depot_ke_asal_json_detail, start_time_leg1_min, time_step_min, legend_anim_label, hover_text)
            animation_frames.extend(frames_leg1)

        if p_obj.rute_json_detail:
            start_time_leg2_min = p_obj.waktu_keberangkatan_dari_asal / 60 if p_obj.waktu_keberangkatan_dari_asal > 0 else (p_obj.waktu_mulai_muat / 60)
            frames_leg2 = _create_animation_frames_for_segment(
                p_obj.rute_json_detail, start_time_leg2_min, time_step_min, legend_anim_label, hover_text)
            animation_frames.extend(frames_leg2)
    if not animation_frames: return pd.DataFrame()
    
    df = pd.DataFrame(animation_frames)
    df['frame_id'] = (df['time_sim_min'] / time_step_min).round().astype(int)
    
    # 1. Urutkan berdasarkan waktu agar 'last' adalah titik ter-update dalam satu frame.
    df = df.sort_values('time_sim_min')
    
    # 2. Hapus duplikat berdasarkan frame dan label truk, pertahankan posisi terakhir 
    df = df.drop_duplicates(subset=['frame_id', 'legend_anim_label'], keep='last')
    
    # 3. Kembalikan DataFrame yang sudah bersih dan terurut untuk visualisasi.
    return df.sort_values(by=['frame_id', 'legend_anim_label']).reset_index(drop=True)
def save_dynamic_log_map_html(fig: go.Figure, animation_events: Dict, run_number: int, save_dir: str, filename_prefix="Visualisasi_Animasi_Log_Dinamis"):
    """
    PERBAIKAN TOTAL: Menyimpan peta animasi dengan panel log dinamis menggunakan
    struktur HTML, CSS, dan JavaScript yang benar dan kokoh.
    """
    os.makedirs(save_dir, exist_ok=True)
    filepath = os.path.join(save_dir, f"{filename_prefix}_{run_number}.html")
    
    events_json = json.dumps(animation_events)
    
    # 1. Konversi figur Plotly menjadi div HTML, tanpa menyertakan tag <html> atau <body>
    fig_div = fig.to_html(full_html=False, include_plotlyjs='cdn', div_id='plotly-div')

    # 2. Definisi struktur HTML, CSS, dan JavaScript 
    final_html = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="utf-8" />
        <title>Visualisasi Simulasi Logistik Dinamis (Run {run_number})</title>
        <style>
            /* CSS diletakkan di dalam <head> untuk struktur yang benar */
            body {{ 
                display: flex; 
                flex-direction: row; 
                height: 100vh; 
                width: 100vw;
                margin: 0; 
                font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
                overflow: hidden; /* Mencegah scrollbar di body */
            }}
            #plotly-container {{ 
                flex-grow: 1; /* Mengambil sisa ruang */
                height: 100%; 
            }}
            #log-panel-container {{ 
                width: 350px; /* Lebar tetap untuk panel log */
                flex-shrink: 0; /* Mencegah panel menyusut */
                padding: 15px; 
                background-color: #f4f4f9; 
                border-left: 1px solid #ddd;
                display: flex; 
                flex-direction: column; 
                height: 100%; 
                box-sizing: border-box;
            }}
            #log-panel {{ 
                overflow-y: auto; 
                flex-grow: 1; 
                background-color: #ffffff; 
                border: 1px solid #ccc;
                padding: 10px; 
                margin-top: 10px;
                border-radius: 5px;
                scroll-behavior: smooth;
            }}
            #log-panel p {{ 
                margin: 2px 0 8px 0; 
                padding: 8px; 
                border-radius: 4px; 
                font-size: 13px; 
                line-height: 1.4;
                border-left: 5px solid #ccc;
            }}
            #summary-container {{
                visibility: hidden; /* Disembunyikan sampai frame terakhir */
                margin-top: 15px; 
                padding-top: 15px; 
                border-top: 2px solid #333;
                flex-shrink: 0;
            }}
            .log-ontime {{ background-color: #e6ffed; border-left-color: #2ca02c; }}
            .log-late {{ background-color: #fff3e0; border-left-color: #ff7f0e; }}
            .log-failed {{ background-color: #ffebee; border-left-color: #d62728; }}
            h3 {{ margin-top: 0; color: #333; }}
            /* Memastikan div plotly mengisi container */
            #plotly-div {{
                height: 100%;
                width: 100%;
            }}
        </style>
    </head>
    <body>
        <!-- 3. Struktur layout utama menggunakan Flexbox -->
        <div id="plotly-container">
            {fig_div}
        </div>
        <div id="log-panel-container">
            <h3>Log Status Pengiriman</h3>
            <div id="log-panel"></div>
            <div id="summary-container">
                <h3>Rangkuman Akhir</h3>
                <div id="shipment-summary" style="font-size: 14px;"></div>
                <div id="truck-summary" style="margin-top: 10px; font-size: 14px;"></div>
            </div>
        </div>

        <script type='text/javascript'>
            // 4. JavaScript disederhanakan, tidak perlu lagi memanipulasi DOM
            const ANIMATION_EVENTS = {events_json};
            const maxFrame = ANIMATION_EVENTS.max_frame;
            
            // Fungsi ini sekarang lebih sederhana dan andal
            function setupDynamicLog() {{
                const graphDiv = document.getElementById('plotly-div');
                if (!graphDiv) {{
                    console.error("Plotly div ('plotly-div') not found!");
                    return;
                }}
                
                let processedFrames = new Set();
                const logPanel = document.getElementById('log-panel');

                graphDiv.on('plotly_afterplot', function() {{
                    try {{
                        if (!graphDiv.layout || !graphDiv.layout.sliders) return;
                        
                        const frameNumber = graphDiv.layout.sliders[0].active;
                        
                        // Hanya tambahkan log untuk frame yang belum diproses
                        for (let i = 0; i <= frameNumber; i++) {{
                            if (!processedFrames.has(i) && ANIMATION_EVENTS.shipments[i]) {{
                                ANIMATION_EVENTS.shipments[i].forEach(event => {{
                                    const p = document.createElement('p');
                                    p.innerHTML = event.message;
                                    p.className = event.css_class;
                                    logPanel.appendChild(p);
                                }});
                                processedFrames.add(i);
                            }}
                        }}

                        // Auto-scroll ke bawah hanya jika pengguna sudah di bawah
                        if(logPanel.scrollTop + logPanel.clientHeight >= logPanel.scrollHeight - 50) {{
                           logPanel.scrollTop = logPanel.scrollHeight;
                        }}

                        // Tampilkan rangkuman di frame terakhir
                        const summaryContainer = document.getElementById('summary-container');
                        if (frameNumber === maxFrame && summaryContainer.style.visibility !== 'visible') {{
                            document.getElementById('shipment-summary').innerHTML = ANIMATION_EVENTS.summary.shipments;
                            document.getElementById('truck-summary').innerHTML = ANIMATION_EVENTS.summary.trucks;
                            summaryContainer.style.visibility = 'visible';
                        }}
                    }} catch (e) {{
                        console.error("Error in plotly_afterplot:", e);
                    }}
                }});

                // Panggil sekali di awal untuk mengisi log frame 0
                setTimeout(() => {{
                    if (graphDiv.emit) {{
                        graphDiv.emit('plotly_afterplot');
                    }}
                }}, 500);
            }}

            // Jalankan setup setelah halaman dimuat
            window.addEventListener('load', setupDynamicLog);
        </script>
    </body>
    </html>
    """
    
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(final_html)
        return filepath
    except Exception as e:
        print(f"Error menyimpan peta dinamis: {e}")
        return None
# ==== Fungsi Skenario Simulasi ====
def jalankan_simulasi_dasar(routing_mode: str, avoid_traffic: bool, run_number: int) -> Tuple[List[Dict], List[Pengiriman]]:
    waktu_simulasi_detik = 0.0
    antrian_pengiriman_sorted = sorted([p for p in daftar_pengiriman_global if p.status_pengiriman == "menunggu_alokasi_truk"], key=lambda p: p.waktu_permintaan_dibuat)
    _pengiriman_diproses_internal: List[Pengiriman] = list(daftar_pengiriman_global)
    _hasil_trip_simulasi_internal: List[Dict] = []
    
    for truk_unit in armada_truk_global:
        truk_unit.waktu_event_selanjutnya = 0; truk_unit.lokasi_sekarang = truk_unit.lokasi_depot
        truk_unit.koordinat_sekarang = (KOTA_KOORDINAT[truk_unit.lokasi_depot][0], KOTA_KOORDINAT[truk_unit.lokasi_depot][1])
        truk_unit.status = "siaga_di_depot"
        truk_unit.muatan_saat_ini_ton = 0; truk_unit.jadwal_tugas_statis = []; truk_unit.tur_konsolidasi_saat_ini = []
        truk_unit.pengiriman_saat_ini_id = None

    processed_pengiriman_ids_dasar = set()
    for pengiriman_obj_global_ref in antrian_pengiriman_sorted:
        pengiriman_obj = next((p_list for p_list in _pengiriman_diproses_internal if p_list.id_pengiriman == pengiriman_obj_global_ref.id_pengiriman), None)
        if not pengiriman_obj or pengiriman_obj.id_pengiriman in processed_pengiriman_ids_dasar or pengiriman_obj.status_pengiriman != "menunggu_alokasi_truk":
            continue

        if pengiriman_obj.waktu_permintaan_dibuat > waktu_simulasi_detik: waktu_simulasi_detik = pengiriman_obj.waktu_permintaan_dibuat
        truk_terpilih = None
        armada_truk_global.sort(key=lambda t: t.waktu_event_selanjutnya)
        for truk_unit_iter in armada_truk_global:
            if truk_unit_iter.apakah_siaga_untuk_tugas_baru(waktu_simulasi_detik) and truk_unit_iter.bisa_angkut(pengiriman_obj.jumlah_barang_ton):
                truk_terpilih = truk_unit_iter; break
        
        if truk_terpilih:
            processed_pengiriman_ids_dasar.add(pengiriman_obj.id_pengiriman)
            waktu_mulai_proses_truk = max(waktu_simulasi_detik, truk_terpilih.waktu_event_selanjutnya)
            
            if truk_terpilih.lokasi_sekarang != pengiriman_obj.kota_asal:
                rute_ke_muatan_detail = get_route_for_segment(truk_terpilih.lokasi_sekarang, pengiriman_obj.kota_asal, routing_mode, avoid_traffic)
                if rute_ke_muatan_detail and "summary" in rute_ke_muatan_detail:
                    pengiriman_obj.rute_depot_ke_asal_json_detail = rute_ke_muatan_detail
                    s_k_m=rute_ke_muatan_detail["summary"]; w_t_k_m_d=s_k_m["travelTimeInSeconds"]; j_k_m_km=s_k_m["lengthInMeters"]/1000
                    b_bbm_k,b_sopir_k,_=hitung_biaya_segmen_perjalanan(j_k_m_km,w_t_k_m_d/3600)
                    truk_terpilih.total_biaya_bbm+=b_bbm_k; truk_terpilih.total_biaya_sopir+=b_sopir_k
                    waktu_mulai_proses_truk+=w_t_k_m_d; truk_terpilih.total_km_operasional+=j_k_m_km; truk_terpilih.total_jam_operasional_mengemudi+=w_t_k_m_d/3600
                    truk_terpilih.lokasi_sekarang=pengiriman_obj.kota_asal
                    truk_terpilih.koordinat_sekarang=(KOTA_KOORDINAT[pengiriman_obj.kota_asal][0], KOTA_KOORDINAT[pengiriman_obj.kota_asal][1])
                else: pengiriman_obj.status_pengiriman="gagal_rute_ke_muatan"; truk_terpilih.waktu_event_selanjutnya=waktu_mulai_proses_truk; continue
            
            pengiriman_obj.truk_yang_ditugaskan_id=truk_terpilih.id_truk; pengiriman_obj.status_pengiriman="dialokasikan_ke_truk"; pengiriman_obj.waktu_truk_dialokasikan=waktu_mulai_proses_truk
            truk_terpilih.status="menunggu_muat"; truk_terpilih.pengiriman_saat_ini_id = pengiriman_obj.id_pengiriman
            rute_utama_detail = get_route_for_segment(pengiriman_obj.kota_asal, pengiriman_obj.kota_tujuan, routing_mode, avoid_traffic)
            if rute_utama_detail and "summary" in rute_utama_detail:
                pengiriman_obj.rute_json_detail=rute_utama_detail
                hasil_trip=simulate_actual_trip(pengiriman_obj,truk_terpilih,rute_utama_detail["summary"],pengiriman_obj.waktu_truk_dialokasikan)
                _hasil_trip_simulasi_internal.append(hasil_trip); waktu_simulasi_detik=max(waktu_simulasi_detik,truk_terpilih.waktu_event_selanjutnya)
            else:
                pengiriman_obj.status_pengiriman="gagal_rute_utama"; truk_terpilih.status="siaga_di_depot"; truk_terpilih.waktu_event_selanjutnya=pengiriman_obj.waktu_truk_dialokasikan
        else:
            if pengiriman_obj.status_pengiriman=="menunggu_alokasi_truk": pengiriman_obj.status_pengiriman="tidak_ada_truk_tersedia"
    for p_obj_global_final in _pengiriman_diproses_internal:
        if p_obj_global_final.id_pengiriman not in processed_pengiriman_ids_dasar and p_obj_global_final.status_pengiriman == "menunggu_alokasi_truk":
            p_obj_global_final.status_pengiriman = "tidak_terproses_final_dasar"
            
    return _hasil_trip_simulasi_internal, _pengiriman_diproses_internal

def jalankan_skenario1_rute_tetap_penjadwalan_statis(routing_mode_s1: str, avoid_traffic_s1: bool, run_number: int) -> Tuple[List[Dict], List[Pengiriman]]:
    _pengiriman_diproses_s1: List[Pengiriman] = list(daftar_pengiriman_global)
    _hasil_trip_simulasi_s1: List[Dict] = []
    jadwal_per_truk = defaultdict(list)
    pengiriman_utk_jadwal = sorted([p for p in _pengiriman_diproses_s1 if p.status_pengiriman == "menunggu_alokasi_truk"], key=lambda p: p.waktu_permintaan_dibuat)
    
    temp_armada_s1 = list(armada_truk_global)
    for p_obj in pengiriman_utk_jadwal:
        truk_terpilih_jadwal = None
        temp_armada_s1.sort(key=lambda t: len(jadwal_per_truk.get(t.id_truk, [])))
        for truk_u in temp_armada_s1:
            if not jadwal_per_truk[truk_u.id_truk] and truk_u.bisa_angkut(p_obj.jumlah_barang_ton):
                jadwal_per_truk[truk_u.id_truk].append(p_obj)
                p_obj.truk_yang_ditugaskan_id = truk_u.id_truk
                p_obj.status_pengiriman = "dijadwalkan_statis_s1"
                truk_terpilih_jadwal = truk_u
                break
        if not truk_terpilih_jadwal: p_obj.status_pengiriman = "tidak_terjadwal_statis_s1"
    
    for truk_u in armada_truk_global:
        truk_u.jadwal_tugas_statis=jadwal_per_truk.get(truk_u.id_truk,[]); truk_u.indeks_tugas_statis_saat_ini=0
        truk_u.waktu_event_selanjutnya=0; truk_u.lokasi_sekarang=truk_u.lokasi_depot; truk_u.koordinat_sekarang=(KOTA_KOORDINAT[truk_u.lokasi_depot][0], KOTA_KOORDINAT[truk_u.lokasi_depot][1])
        truk_u.status="siaga_di_depot"; truk_u.muatan_saat_ini_ton=0

    events_s1: List[Tuple[float, str, str]] = []
    for truk_u in armada_truk_global:
        if truk_u.jadwal_tugas_statis: events_s1.append((0, "CEK_TUGAS_STATIS_S1", truk_u.id_truk))
    events_s1.sort()
    
    waktu_simulasi_s1_detik = 0.0
    processed_event_pengiriman_ids_s1 = set()

    while events_s1:
        waktu_event, tipe_event_s1, id_entitas = events_s1.pop(0)
        waktu_simulasi_s1_detik = max(waktu_simulasi_s1_detik, waktu_event)
        
        truk_event: Optional[Truk] = None
        pengiriman_event_obj: Optional[Pengiriman] = None

        if id_entitas.startswith("T"): truk_event = next((t for t in armada_truk_global if t.id_truk == id_entitas), None)
        elif id_entitas.startswith("P"):
            pengiriman_event_obj = next((p for p in _pengiriman_diproses_s1 if p.id_pengiriman == id_entitas), None)
            if pengiriman_event_obj and pengiriman_event_obj.truk_yang_ditugaskan_id:
                truk_event = next((t for t in armada_truk_global if t.id_truk == pengiriman_event_obj.truk_yang_ditugaskan_id), None)
        
        if not truk_event and not pengiriman_event_obj: continue

        if tipe_event_s1 == "CEK_TUGAS_STATIS_S1" and truk_event:
            if truk_event.status in ["siaga_di_depot","siaga_setelah_bongkar"] and truk_event.indeks_tugas_statis_saat_ini < len(truk_event.jadwal_tugas_statis):
                p_obj_s1 = truk_event.jadwal_tugas_statis[truk_event.indeks_tugas_statis_saat_ini]
                if p_obj_s1.id_pengiriman in processed_event_pengiriman_ids_s1: continue
                waktu_mulai = max(waktu_simulasi_s1_detik, p_obj_s1.waktu_permintaan_dibuat)
                processed_event_pengiriman_ids_s1.add(p_obj_s1.id_pengiriman); next_event_time = waktu_mulai
                if truk_event.lokasi_sekarang != p_obj_s1.kota_asal:
                    rute_muat = get_route_for_segment(truk_event.lokasi_sekarang, p_obj_s1.kota_asal, routing_mode_s1, avoid_traffic_s1)
                    if rute_muat and "summary" in rute_muat:
                        p_obj_s1.rute_depot_ke_asal_json_detail = rute_muat
                        s_m=rute_muat["summary"]; w_m_d=s_m["travelTimeInSeconds"]; j_m_km=s_m["lengthInMeters"]/1000
                        b_bbm_m,b_sopir_m,_=hitung_biaya_segmen_perjalanan(j_m_km,w_m_d/3600);truk_event.total_biaya_bbm+=b_bbm_m;truk_event.total_biaya_sopir+=b_sopir_m
                        next_event_time+=w_m_d;truk_event.total_km_operasional+=j_m_km;truk_event.total_jam_operasional_mengemudi+=w_m_d/3600
                        truk_event.lokasi_sekarang=p_obj_s1.kota_asal
                        truk_event.koordinat_sekarang=(KOTA_KOORDINAT[p_obj_s1.kota_asal][0], KOTA_KOORDINAT[p_obj_s1.kota_asal][1])
                    else: p_obj_s1.status_pengiriman=f"gagal_rute_muat_s1_{p_obj_s1.id_pengiriman}";truk_event.indeks_tugas_statis_saat_ini+=1;events_s1.append((next_event_time,"CEK_TUGAS_STATIS_S1",truk_event.id_truk));events_s1.sort();continue
                p_obj_s1.waktu_truk_dialokasikan=next_event_time;truk_event.status="menunggu_muat_s1";truk_event.pengiriman_saat_ini_id=p_obj_s1.id_pengiriman
                events_s1.append((next_event_time,"MULAI_MUAT_S1",p_obj_s1.id_pengiriman));events_s1.sort()
        elif tipe_event_s1 == "MULAI_MUAT_S1" and pengiriman_event_obj and truk_event:
            truk_event.status="memuat_barang";pengiriman_event_obj.waktu_mulai_muat=waktu_simulasi_s1_detik;w_m_d=pengiriman_event_obj.estimasi_waktu_pengambilan_barang_menit*60
            pengiriman_event_obj.waktu_selesai_muat=waktu_simulasi_s1_detik+w_m_d;truk_event.total_jam_operasional_memuat+=w_m_d/3600
            events_s1.append((pengiriman_event_obj.waktu_selesai_muat,"SELESAI_MUAT_S1",pengiriman_event_obj.id_pengiriman));events_s1.sort()
        elif tipe_event_s1 == "SELESAI_MUAT_S1" and pengiriman_event_obj and truk_event:
            truk_event.muatan_saat_ini_ton=pengiriman_event_obj.jumlah_barang_ton;pengiriman_event_obj.waktu_keberangkatan_dari_asal=waktu_simulasi_s1_detik
            r_u_d=get_route_for_segment(pengiriman_event_obj.kota_asal,pengiriman_event_obj.kota_tujuan,routing_mode_s1,avoid_traffic_s1)
            if r_u_d and "summary" in r_u_d:
                pengiriman_event_obj.rute_json_detail=r_u_d;s_u=r_u_d["summary"];w_t_u_d=s_u["travelTimeInSeconds"];j_u_km=s_u["lengthInMeters"]/1000
                b_bbm_u,b_sopir_u,_=hitung_biaya_segmen_perjalanan(j_u_km,w_t_u_d/3600);truk_event.total_biaya_bbm+=b_bbm_u;truk_event.total_biaya_sopir+=b_sopir_u;pengiriman_event_obj.biaya_pengiriman_total+=(b_bbm_u+b_sopir_u)
                truk_event.total_km_operasional+=j_u_km;truk_event.total_jam_operasional_mengemudi+=w_t_u_d/3600;pengiriman_event_obj.jarak_tempuh_km=j_u_km;pengiriman_event_obj.estimasi_waktu_tempuh_menit=w_t_u_d/60
                truk_event.status="dalam_perjalanan_mengantar";events_s1.append((waktu_simulasi_s1_detik+w_t_u_d,"TIBA_TUJUAN_S1",pengiriman_event_obj.id_pengiriman))
            else:pengiriman_event_obj.status_pengiriman="gagal_rute_utama_s1";truk_event.status="siaga_di_depot";truk_event.indeks_tugas_statis_saat_ini+=1;events_s1.append((waktu_simulasi_s1_detik,"CEK_TUGAS_STATIS_S1",truk_event.id_truk))
            events_s1.sort()
        elif tipe_event_s1 == "TIBA_TUJUAN_S1" and pengiriman_event_obj and truk_event:
            truk_event.lokasi_sekarang=pengiriman_event_obj.kota_tujuan;truk_event.koordinat_sekarang=(KOTA_KOORDINAT[pengiriman_event_obj.kota_tujuan][0], KOTA_KOORDINAT[pengiriman_event_obj.kota_tujuan][1]);pengiriman_event_obj.waktu_sampai_tujuan=waktu_simulasi_s1_detik;truk_event.status="menunggu_bongkar_s1"
            events_s1.append((waktu_simulasi_s1_detik,"MULAI_BONGKAR_S1",pengiriman_event_obj.id_pengiriman));events_s1.sort()
        elif tipe_event_s1 == "MULAI_BONGKAR_S1" and pengiriman_event_obj and truk_event:
            truk_event.status="membongkar_barang";pengiriman_event_obj.waktu_mulai_bongkar=waktu_simulasi_s1_detik;w_b_d=pengiriman_event_obj.estimasi_waktu_bongkar_menit*60
            pengiriman_event_obj.waktu_selesai_bongkar=waktu_simulasi_s1_detik+w_b_d;truk_event.total_jam_operasional_membongkar+=w_b_d/60
            events_s1.append((pengiriman_event_obj.waktu_selesai_bongkar,"SELESAI_BONGKAR_S1",pengiriman_event_obj.id_pengiriman));events_s1.sort()
        elif tipe_event_s1 == "SELESAI_BONGKAR_S1" and pengiriman_event_obj and truk_event:
            proses_event_bongkar_selesai(truk_event,pengiriman_event_obj,waktu_simulasi_s1_detik)
            _hasil_trip_simulasi_s1.append({"id_pengiriman":pengiriman_event_obj.id_pengiriman,"id_truk":truk_event.id_truk,"asal":pengiriman_event_obj.kota_asal,"tujuan":pengiriman_event_obj.kota_tujuan,"jarak_km":pengiriman_event_obj.jarak_tempuh_km,"waktu_tempuh_aktual_menit":pengiriman_event_obj.estimasi_waktu_tempuh_menit,"waktu_muat_menit":pengiriman_event_obj.estimasi_waktu_pengambilan_barang_menit,"waktu_bongkar_menit":pengiriman_event_obj.estimasi_waktu_bongkar_menit,"total_waktu_siklus_pengiriman_menit":(pengiriman_event_obj.waktu_penyelesaian_aktual-pengiriman_event_obj.waktu_mulai_muat)/60 if pengiriman_event_obj.waktu_mulai_muat > 0 else -1,"status_akhir_pengiriman":pengiriman_event_obj.status_pengiriman,"biaya_total_trip":pengiriman_event_obj.biaya_pengiriman_total,"waktu_permintaan_dibuat_jam":pengiriman_event_obj.waktu_permintaan_dibuat/3600,"waktu_selesai_aktual_jam":pengiriman_event_obj.waktu_penyelesaian_aktual/3600,"deadline_sla_jam":pengiriman_event_obj.deadline_penyelesaian/3600})
            truk_event.indeks_tugas_statis_saat_ini+=1;truk_event.waktu_event_selanjutnya=waktu_simulasi_s1_detik;truk_event.status="siaga_setelah_bongkar"
            events_s1.append((waktu_simulasi_s1_detik,"CEK_TUGAS_STATIS_S1",truk_event.id_truk));events_s1.sort()
            
    return _hasil_trip_simulasi_s1, _pengiriman_diproses_s1

def jalankan_skenario2_rute_dinamis_penjadwalan_intertruck(avoid_traffic_s2: bool, run_number: int, routing_mode_s2: str) -> Tuple[List[Dict], List[Pengiriman]]:
    _pengiriman_diproses_s2: List[Pengiriman] = list(daftar_pengiriman_global)
    _hasil_trip_simulasi_s2: List[Dict] = []
    for truk_unit in armada_truk_global: truk_unit.waktu_event_selanjutnya=0; truk_unit.lokasi_sekarang=truk_unit.lokasi_depot; truk_unit.koordinat_sekarang=(KOTA_KOORDINAT[truk_unit.lokasi_depot][0], KOTA_KOORDINAT[truk_unit.lokasi_depot][1]); truk_unit.status="siaga_di_depot"; truk_unit.muatan_saat_ini_ton=0
    
    events_s2: List[Tuple[float, str, str]] = []
    for p in _pengiriman_diproses_s2: 
        if p.status_pengiriman=="menunggu_alokasi_truk": events_s2.append((p.waktu_permintaan_dibuat,"PERMINTAAN_BARU_S2",p.id_pengiriman))
    for t in armada_truk_global: events_s2.append((0,"TRUK_SIAGA_CEK_TUGAS_S2",t.id_truk))
    events_s2.sort(); waktu_simulasi_detik=0.0; processed_pengiriman_ids_in_event_loop_s2=set()
    
    while events_s2:
        waktu_event_saat_ini,tipe_event,data_id=events_s2.pop(0); waktu_simulasi_detik=max(waktu_simulasi_detik,waktu_event_saat_ini)
        truk_event_s2:Optional[Truk]=None; pengiriman_event_s2:Optional[Pengiriman]=None
        
        if isinstance(data_id,str) and data_id.startswith("T"):truk_event_s2=next((t for t in armada_truk_global if t.id_truk==data_id),None)
        elif isinstance(data_id,str) and data_id.startswith("P"):
            pengiriman_event_s2=next((p for p in _pengiriman_diproses_s2 if p.id_pengiriman==data_id),None)
            if pengiriman_event_s2 and pengiriman_event_s2.truk_yang_ditugaskan_id:truk_event_s2=next((t for t in armada_truk_global if t.id_truk==pengiriman_event_s2.truk_yang_ditugaskan_id),None)
        
        if not truk_event_s2 and not pengiriman_event_s2: continue
        
        if tipe_event=="PERMINTAAN_BARU_S2":
            for t_siaga in armada_truk_global:
                if t_siaga.apakah_siaga_untuk_tugas_baru(waktu_simulasi_detik):
                    if not any(ev[1]=="TRUK_SIAGA_CEK_TUGAS_S2" and ev[2]==t_siaga.id_truk and ev[0]<=waktu_simulasi_detik+1 for ev in events_s2):events_s2.append((waktu_simulasi_detik,"TRUK_SIAGA_CEK_TUGAS_S2",t_siaga.id_truk))
            events_s2.sort()
        elif tipe_event=="TRUK_SIAGA_CEK_TUGAS_S2" and truk_event_s2:
            if not truk_event_s2.apakah_siaga_untuk_tugas_baru(waktu_simulasi_detik):continue
            pengiriman_belum_diproses_s2=sorted([p for p in _pengiriman_diproses_s2 if p.status_pengiriman=="menunggu_alokasi_truk" and p.waktu_permintaan_dibuat<=waktu_simulasi_detik and p.id_pengiriman not in processed_pengiriman_ids_in_event_loop_s2],key=lambda p:p.deadline_penyelesaian)
            pengiriman_terpilih_untuk_truk=None;min_estimasi_waktu_ke_pickup=float('inf')
            for p_obj_cek in pengiriman_belum_diproses_s2:
                if truk_event_s2.bisa_angkut(p_obj_cek.jumlah_barang_ton):
                    waktu_tempuh_ke_muat=0
                    if truk_event_s2.lokasi_sekarang!=p_obj_cek.kota_asal:
                        rute_ke_muat_temp=get_route_for_segment(truk_event_s2.lokasi_sekarang,p_obj_cek.kota_asal,routing_mode_s2,avoid_traffic_s2)
                        if rute_ke_muat_temp and "summary" in rute_ke_muat_temp:waktu_tempuh_ke_muat=rute_ke_muat_temp["summary"]["travelTimeInSeconds"]
                        else:waktu_tempuh_ke_muat=float('inf')
                    if waktu_tempuh_ke_muat<min_estimasi_waktu_ke_pickup:min_estimasi_waktu_ke_pickup=waktu_tempuh_ke_muat;pengiriman_terpilih_untuk_truk=p_obj_cek
            if pengiriman_terpilih_untuk_truk:
                pengiriman_obj_assign=pengiriman_terpilih_untuk_truk
                processed_pengiriman_ids_in_event_loop_s2.add(pengiriman_obj_assign.id_pengiriman);pengiriman_obj_assign.truk_yang_ditugaskan_id=truk_event_s2.id_truk;pengiriman_obj_assign.status_pengiriman="dialokasikan_ke_truk"
                next_event_time_truk=waktu_simulasi_detik
                if truk_event_s2.lokasi_sekarang!=pengiriman_obj_assign.kota_asal:
                    rute_ke_muatan_detail=get_route_for_segment(truk_event_s2.lokasi_sekarang,pengiriman_obj_assign.kota_asal,routing_mode_s2,avoid_traffic_s2)
                    if rute_ke_muatan_detail and "summary" in rute_ke_muatan_detail:
                        pengiriman_obj_assign.rute_depot_ke_asal_json_detail = rute_ke_muatan_detail
                        s_k_m=rute_ke_muatan_detail["summary"];w_t_k_m_d=s_k_m["travelTimeInSeconds"];j_k_m_km=s_k_m["lengthInMeters"]/1000
                        b_bbm_k,b_sopir_k,_=hitung_biaya_segmen_perjalanan(j_k_m_km,w_t_k_m_d/3600);truk_event_s2.total_biaya_bbm+=b_bbm_k;truk_event_s2.total_biaya_sopir+=b_sopir_k
                        next_event_time_truk+=w_t_k_m_d;truk_event_s2.total_km_operasional+=j_k_m_km;truk_event_s2.total_jam_operasional_mengemudi+=w_t_k_m_d/3600
                        truk_event_s2.lokasi_sekarang=pengiriman_obj_assign.kota_asal;truk_event_s2.koordinat_sekarang=(KOTA_KOORDINAT[pengiriman_obj_assign.kota_asal][0], KOTA_KOORDINAT[pengiriman_obj_assign.kota_asal][1])
                    else:pengiriman_obj_assign.status_pengiriman="gagal_rute_ke_muatan_s2";events_s2.append((next_event_time_truk,"TRUK_SIAGA_CEK_TUGAS_S2",truk_event_s2.id_truk));events_s2.sort();continue
                pengiriman_obj_assign.waktu_truk_dialokasikan=next_event_time_truk;truk_event_s2.status="menunggu_muat_s2";truk_event_s2.pengiriman_saat_ini_id=pengiriman_obj_assign.id_pengiriman
                events_s2.append((next_event_time_truk,"MULAI_MUAT_S2",pengiriman_obj_assign.id_pengiriman));events_s2.sort()
        elif tipe_event=="MULAI_MUAT_S2" and pengiriman_event_s2 and truk_event_s2:
            truk_event_s2.status="memuat_barang";pengiriman_event_s2.waktu_mulai_muat=waktu_simulasi_detik;waktu_muat_detik=pengiriman_event_s2.estimasi_waktu_pengambilan_barang_menit*60
            pengiriman_event_s2.waktu_selesai_muat=waktu_simulasi_detik+waktu_muat_detik;truk_event_s2.total_jam_operasional_memuat+=waktu_muat_detik/3600
            events_s2.append((pengiriman_event_s2.waktu_selesai_muat,"SELESAI_MUAT_S2",pengiriman_event_s2.id_pengiriman));events_s2.sort()
        elif tipe_event=="SELESAI_MUAT_S2" and pengiriman_event_s2 and truk_event_s2:
            truk_event_s2.muatan_saat_ini_ton=pengiriman_event_s2.jumlah_barang_ton;pengiriman_event_s2.waktu_keberangkatan_dari_asal=waktu_simulasi_detik
            rute_utama_detail=get_route_for_segment(pengiriman_event_s2.kota_asal,pengiriman_event_s2.kota_tujuan,routing_mode_s2,avoid_traffic_s2)
            if rute_utama_detail and "summary" in rute_utama_detail:
                pengiriman_event_s2.rute_json_detail=rute_utama_detail;summary_u=rute_utama_detail["summary"];w_t_u_d=summary_u["travelTimeInSeconds"];j_u_km=summary_u["lengthInMeters"]/1000
                b_bbm_u,b_sopir_u,_=hitung_biaya_segmen_perjalanan(j_u_km,w_t_u_d/3600);truk_event_s2.total_biaya_bbm+=b_bbm_u;truk_event_s2.total_biaya_sopir+=b_sopir_u;pengiriman_event_s2.biaya_pengiriman_total+=(b_bbm_u+b_sopir_u)
                truk_event_s2.total_km_operasional+=j_u_km;truk_event_s2.total_jam_operasional_mengemudi+=w_t_u_d/3600;pengiriman_event_s2.jarak_tempuh_km=j_u_km;pengiriman_event_s2.estimasi_waktu_tempuh_menit=w_t_u_d/60
                truk_event_s2.status="dalam_perjalanan_mengantar";events_s2.append((waktu_simulasi_detik+w_t_u_d,"TIBA_TUJUAN_S2",pengiriman_event_s2.id_pengiriman))
            else:pengiriman_event_s2.status_pengiriman="gagal_rute_utama_s2";truk_event_s2.status="siaga_di_depot";events_s2.append((waktu_simulasi_detik,"TRUK_SIAGA_CEK_TUGAS_S2",truk_event_s2.id_truk))
            events_s2.sort()
        elif tipe_event=="TIBA_TUJUAN_S2" and pengiriman_event_s2 and truk_event_s2:
            truk_event_s2.lokasi_sekarang=pengiriman_event_s2.kota_tujuan;truk_event_s2.koordinat_sekarang=(KOTA_KOORDINAT[pengiriman_event_s2.kota_tujuan][0], KOTA_KOORDINAT[pengiriman_event_s2.kota_tujuan][1]);pengiriman_event_s2.waktu_sampai_tujuan=waktu_simulasi_detik;truk_event_s2.status="menunggu_bongkar_s2"
            events_s2.append((waktu_simulasi_detik,"MULAI_BONGKAR_S2",pengiriman_event_s2.id_pengiriman));events_s2.sort()
        elif tipe_event=="MULAI_BONGKAR_S2" and pengiriman_event_s2 and truk_event_s2:
            truk_event_s2.status="membongkar_barang";pengiriman_event_s2.waktu_mulai_bongkar=waktu_simulasi_detik;waktu_bongkar_detik=pengiriman_event_s2.estimasi_waktu_bongkar_menit*60
            pengiriman_event_s2.waktu_selesai_bongkar=waktu_simulasi_detik+waktu_bongkar_detik;truk_event_s2.total_jam_operasional_membongkar+=waktu_bongkar_detik/60
            events_s2.append((pengiriman_event_s2.waktu_selesai_bongkar,"SELESAI_BONGKAR_S2",pengiriman_event_s2.id_pengiriman));events_s2.sort()
        elif tipe_event=="SELESAI_BONGKAR_S2" and pengiriman_event_s2 and truk_event_s2:
            proses_event_bongkar_selesai(truk_event_s2,pengiriman_event_s2,waktu_simulasi_detik)
            _hasil_trip_simulasi_s2.append({"id_pengiriman":pengiriman_event_s2.id_pengiriman,"id_truk":truk_event_s2.id_truk,"asal":pengiriman_event_s2.kota_asal,"tujuan":pengiriman_event_s2.kota_tujuan,"jarak_km":pengiriman_event_s2.jarak_tempuh_km,"waktu_tempuh_aktual_menit":pengiriman_event_s2.estimasi_waktu_tempuh_menit,"waktu_muat_menit":pengiriman_event_s2.estimasi_waktu_pengambilan_barang_menit,"waktu_bongkar_menit":pengiriman_event_s2.estimasi_waktu_bongkar_menit,"total_waktu_siklus_pengiriman_menit":(pengiriman_event_s2.waktu_penyelesaian_aktual-pengiriman_event_s2.waktu_mulai_muat)/60 if pengiriman_event_s2.waktu_mulai_muat>0 else -1,"status_akhir_pengiriman":pengiriman_event_s2.status_pengiriman,"biaya_total_trip":pengiriman_event_s2.biaya_pengiriman_total,"waktu_permintaan_dibuat_jam":pengiriman_event_s2.waktu_permintaan_dibuat/3600,"waktu_selesai_aktual_jam":pengiriman_event_s2.waktu_penyelesaian_aktual/3600,"deadline_sla_jam":pengiriman_event_s2.deadline_penyelesaian/3600})
            truk_event_s2.waktu_event_selanjutnya=waktu_simulasi_detik;truk_event_s2.status="siaga_setelah_bongkar"; truk_event_s2.pengiriman_saat_ini_id = None
            events_s2.append((waktu_simulasi_detik,"TRUK_SIAGA_CEK_TUGAS_S2",truk_event_s2.id_truk));events_s2.sort()
    
    for p_glob in _pengiriman_diproses_s2:
        if p_glob.id_pengiriman not in processed_pengiriman_ids_in_event_loop_s2 and p_glob.status_pengiriman=="menunggu_alokasi_truk":
            p_glob.status_pengiriman="tidak_terproses_s2_final"
            
    return _hasil_trip_simulasi_s2,_pengiriman_diproses_s2

def bentuk_tur_konsolidasi_sederhana(daftar_pengiriman_tersisa: List[Pengiriman], truk: Truk, max_pengiriman_per_tur: int = 2) -> Optional[List[Tuple[Pengiriman, str]]]:
    if not truk.apakah_siaga_untuk_tugas_baru(0): return None
    
    tur_untuk_truk: List[Tuple[Pengiriman, str]] = []
    pengiriman_dalam_tur: List[Pengiriman] = []
    muatan_tur_saat_ini = truk.muatan_saat_ini_ton 
    
    pengiriman_tersisa_valid = sorted(
        [p for p in daftar_pengiriman_tersisa if p.status_pengiriman == "menunggu_alokasi_truk"],
        key=lambda p: p.waktu_permintaan_dibuat
    )

    p_utama = None
    for p in pengiriman_tersisa_valid:
        if truk.bisa_angkut(p.jumlah_barang_ton):
            p_utama = p
            break
    if not p_utama: return None

    pengiriman_dalam_tur.append(p_utama)
    muatan_tur_saat_ini += p_utama.jumlah_barang_ton
    p_utama.status_pengiriman = "dijadwalkan_konsolidasi_s3"
    
    if max_pengiriman_per_tur > 1:
        for p_tambahan in pengiriman_tersisa_valid:
            if len(pengiriman_dalam_tur) >= max_pengiriman_per_tur: break
            if p_tambahan.id_pengiriman != p_utama.id_pengiriman and \
               p_tambahan.status_pengiriman == "menunggu_alokasi_truk" and \
               p_tambahan.kota_asal == p_utama.kota_asal and \
               truk.bisa_angkut(muatan_tur_saat_ini + p_tambahan.jumlah_barang_ton):
                
                pengiriman_dalam_tur.append(p_tambahan)
                muatan_tur_saat_ini += p_tambahan.jumlah_barang_ton
                p_tambahan.status_pengiriman = "dijadwalkan_konsolidasi_s3"

    if not pengiriman_dalam_tur: return None

    kota_asal_tur = pengiriman_dalam_tur[0].kota_asal
    
    for i_p, p_tur in enumerate(pengiriman_dalam_tur):
        tur_untuk_truk.append((p_tur, "pickup"))
        p_tur.urutan_dalam_tur = len(tur_untuk_truk)

    pengiriman_untuk_delivery = sorted(
        pengiriman_dalam_tur,
        key=lambda p_deliv: calculate_haversine_distance(
            KOTA_KOORDINAT[kota_asal_tur][0], KOTA_KOORDINAT[kota_asal_tur][1],
            KOTA_KOORDINAT[p_deliv.kota_tujuan][0], KOTA_KOORDINAT[p_deliv.kota_tujuan][1]
        ) if p_deliv.kota_tujuan in KOTA_KOORDINAT and kota_asal_tur in KOTA_KOORDINAT else float('inf')
    )
    for i_d, p_deliv_tur in enumerate(pengiriman_untuk_delivery):
        tur_untuk_truk.append((p_deliv_tur, "delivery"))
        p_deliv_tur.urutan_dalam_tur = len(pengiriman_dalam_tur) + i_d + 1 
        
    return tur_untuk_truk

def jalankan_skenario3_konsolidasi_pengiriman(routing_mode_s3: str, avoid_traffic_s3: bool, run_number: int) -> Tuple[List[Dict], List[Pengiriman]]:
    _pengiriman_diproses_s3: List[Pengiriman] = list(daftar_pengiriman_global) 
    _hasil_trip_simulasi_s3: List[Dict] = []
    waktu_simulasi_global = 0.0 

    for truk_unit in armada_truk_global: 
        truk_unit.waktu_event_selanjutnya=0; truk_unit.lokasi_sekarang=truk_unit.lokasi_depot; truk_unit.koordinat_sekarang=(KOTA_KOORDINAT[truk_unit.lokasi_depot][0], KOTA_KOORDINAT[truk_unit.lokasi_depot][1])
        truk_unit.status="siaga_di_depot"; truk_unit.muatan_saat_ini_ton=0; truk_unit.tur_konsolidasi_saat_ini=[]; truk_unit.indeks_waypoint_tur_saat_ini=0

    loop_tur_formation = True
    while loop_tur_formation:
        loop_tur_formation = False 
        pengiriman_tersisa_untuk_tur = sorted([p for p in _pengiriman_diproses_s3 if p.status_pengiriman == "menunggu_alokasi_truk"], key=lambda p:p.waktu_permintaan_dibuat)
        if not pengiriman_tersisa_untuk_tur: break

        for truk_unit in armada_truk_global:
            if truk_unit.apakah_siaga_untuk_tugas_baru(waktu_simulasi_global) and not truk_unit.tur_konsolidasi_saat_ini: 
                tur_baru = bentuk_tur_konsolidasi_sederhana(pengiriman_tersisa_untuk_tur, truk_unit) 
                if tur_baru:
                    truk_unit.tur_konsolidasi_saat_ini = tur_baru
                    truk_unit.status = "ditugaskan_tur_s3" 
                    truk_unit.indeks_waypoint_tur_saat_ini = 0
                    loop_tur_formation = True 
                    for wp_p, _ in tur_baru: wp_p.truk_yang_ditugaskan_id = truk_unit.id_truk
    
    events_s3: List[Tuple[float, str, str]] = [] 
    for truk_unit in armada_truk_global:
        if truk_unit.tur_konsolidasi_saat_ini and truk_unit.status == "ditugaskan_tur_s3":
            waktu_mulai_tur_truk = truk_unit.waktu_event_selanjutnya 
            for p_tur, _ in truk_unit.tur_konsolidasi_saat_ini:
                waktu_mulai_tur_truk = max(waktu_mulai_tur_truk, p_tur.waktu_permintaan_dibuat)
            
            events_s3.append((waktu_mulai_tur_truk, "LANJUT_TUR_S3", truk_unit.id_truk))
    events_s3.sort()

    processed_waypoint_ids_s3 = set() 

    while events_s3:
        waktu_event, tipe_event, id_truk_event = events_s3.pop(0)
        waktu_simulasi_global = max(waktu_simulasi_global, waktu_event)
        
        truk_event = next((t for t in armada_truk_global if t.id_truk == id_truk_event), None)
        if not truk_event or truk_event.status == "siaga_setelah_tur": continue 

        if tipe_event == "LANJUT_TUR_S3":
            if not truk_event.tur_konsolidasi_saat_ini or truk_event.indeks_waypoint_tur_saat_ini >= len(truk_event.tur_konsolidasi_saat_ini):
                truk_event.status = "siaga_setelah_tur"
                continue 

            current_truk_time_for_wp = waktu_simulasi_global 
            pengiriman_obj_wp, tipe_wp = truk_event.tur_konsolidasi_saat_ini[truk_event.indeks_waypoint_tur_saat_ini]
            waypoint_unique_id = (truk_event.id_truk, pengiriman_obj_wp.id_pengiriman, tipe_wp, truk_event.indeks_waypoint_tur_saat_ini)

            if waypoint_unique_id in processed_waypoint_ids_s3: continue
            processed_waypoint_ids_s3.add(waypoint_unique_id)

            kota_wp_target = pengiriman_obj_wp.kota_asal if tipe_wp == "pickup" else pengiriman_obj_wp.kota_tujuan
            
            truk_event.status = f"menuju_{tipe_wp}_{pengiriman_obj_wp.id_pengiriman}_s3"
            waktu_setelah_aktivitas = current_truk_time_for_wp

            if truk_event.lokasi_sekarang != kota_wp_target:
                rute_detail_wp = get_route_for_segment(truk_event.lokasi_sekarang, kota_wp_target, routing_mode_s3, avoid_traffic_s3)
                if rute_detail_wp and "summary" in rute_detail_wp:
                    if truk_event.indeks_waypoint_tur_saat_ini == 0:
                        pengiriman_obj_wp.rute_depot_ke_asal_json_detail = rute_detail_wp
                    
                    summary_wp_leg = rute_detail_wp["summary"]; waktu_tempuh_detik_wp_leg = summary_wp_leg["travelTimeInSeconds"]; jarak_km_wp_leg = summary_wp_leg["lengthInMeters"]/1000
                    b_bbm_wp_l,b_sopir_wp_l,_ = hitung_biaya_segmen_perjalanan(jarak_km_wp_leg, waktu_tempuh_detik_wp_leg/3600)
                    
                    pengiriman_aktif_dlm_muatan = [p_tur for p_tur,tipe_p in truk_event.tur_konsolidasi_saat_ini[:truk_event.indeks_waypoint_tur_saat_ini+1] if tipe_p=="pickup" and p_tur.is_pickup_completed and not p_tur.is_delivery_completed]
                    if not pengiriman_aktif_dlm_muatan and tipe_wp == "pickup" : pengiriman_aktif_dlm_muatan = [pengiriman_obj_wp]
                    
                    if pengiriman_aktif_dlm_muatan:
                        biaya_per_p_aktif_leg = (b_bbm_wp_l+b_sopir_wp_l)/len(pengiriman_aktif_dlm_muatan)
                        for p_a_leg in pengiriman_aktif_dlm_muatan: p_a_leg.biaya_pengiriman_total += biaya_per_p_aktif_leg
                    
                    truk_event.total_biaya_bbm+=b_bbm_wp_l; truk_event.total_biaya_sopir+=b_sopir_wp_l
                    waktu_setelah_aktivitas+=waktu_tempuh_detik_wp_leg; truk_event.total_km_operasional+=jarak_km_wp_leg; truk_event.total_jam_operasional_mengemudi+=waktu_tempuh_detik_wp_leg/3600
                else: 
                    for p_tur_gagal, _ in truk_event.tur_konsolidasi_saat_ini[truk_event.indeks_waypoint_tur_saat_ini:]:
                        if not p_tur_gagal.is_delivery_completed: p_tur_gagal.status_pengiriman=f"gagal_tur_rute_s3"
                    truk_event.tur_konsolidasi_saat_ini=[];truk_event.status="siaga_di_depot";truk_event.waktu_event_selanjutnya=waktu_setelah_aktivitas; 
                    continue
            
            truk_event.lokasi_sekarang=kota_wp_target; truk_event.koordinat_sekarang=(KOTA_KOORDINAT[kota_wp_target][0], KOTA_KOORDINAT[kota_wp_target][1])
            
            if tipe_wp=="pickup":
                pengiriman_obj_wp.waktu_mulai_muat=waktu_setelah_aktivitas; waktu_muat_detik_wp_val=pengiriman_obj_wp.estimasi_waktu_pengambilan_barang_menit*60
                proses_event_muat_selesai(truk_event,pengiriman_obj_wp,waktu_setelah_aktivitas+waktu_muat_detik_wp_val)
                waktu_setelah_aktivitas=pengiriman_obj_wp.waktu_selesai_muat; pengiriman_obj_wp.waktu_keberangkatan_dari_asal=waktu_setelah_aktivitas
                truk_event.status = f"selesai_muat_{pengiriman_obj_wp.id_pengiriman}_s3"
            elif tipe_wp=="delivery":
                pengiriman_obj_wp.waktu_sampai_tujuan=waktu_setelah_aktivitas; pengiriman_obj_wp.waktu_mulai_bongkar=waktu_setelah_aktivitas
                waktu_bongkar_detik_wp_val=pengiriman_obj_wp.estimasi_waktu_bongkar_menit*60
                proses_event_bongkar_selesai(truk_event,pengiriman_obj_wp,waktu_setelah_aktivitas+waktu_bongkar_detik_wp_val)
                waktu_setelah_aktivitas=pengiriman_obj_wp.waktu_selesai_bongkar
                truk_event.status = f"selesai_bongkar_{pengiriman_obj_wp.id_pengiriman}_s3"
                if pengiriman_obj_wp.is_pickup_completed:
                    temp_asal_coord = KOTA_KOORDINAT.get(pengiriman_obj_wp.kota_asal)
                    temp_tujuan_coord = KOTA_KOORDINAT.get(pengiriman_obj_wp.kota_tujuan)
                    if temp_asal_coord and temp_tujuan_coord:
                        pengiriman_obj_wp.jarak_tempuh_km=calculate_haversine_distance(temp_asal_coord[0],temp_asal_coord[1],temp_tujuan_coord[0],temp_tujuan_coord[1])
                        pengiriman_obj_wp.rute_json_detail=estimasi_rute_internal((temp_asal_coord[0], temp_asal_coord[1]),(temp_tujuan_coord[0], temp_tujuan_coord[1]))
                    
                    pengiriman_obj_wp.estimasi_waktu_tempuh_menit=(pengiriman_obj_wp.waktu_sampai_tujuan-pengiriman_obj_wp.waktu_keberangkatan_dari_asal)/60 if pengiriman_obj_wp.waktu_keberangkatan_dari_asal>0 and pengiriman_obj_wp.waktu_sampai_tujuan>pengiriman_obj_wp.waktu_keberangkatan_dari_asal else -1
                    
                    _hasil_trip_simulasi_s3.append({"id_pengiriman":pengiriman_obj_wp.id_pengiriman,"id_truk":truk_event.id_truk,"asal":pengiriman_obj_wp.kota_asal,"tujuan":pengiriman_obj_wp.kota_tujuan,"jarak_km":pengiriman_obj_wp.jarak_tempuh_km,"waktu_tempuh_aktual_menit":pengiriman_obj_wp.estimasi_waktu_tempuh_menit,"waktu_muat_menit":pengiriman_obj_wp.estimasi_waktu_pengambilan_barang_menit,"waktu_bongkar_menit":pengiriman_obj_wp.estimasi_waktu_bongkar_menit,"total_waktu_siklus_pengiriman_menit":(pengiriman_obj_wp.waktu_penyelesaian_aktual-pengiriman_obj_wp.waktu_mulai_muat)/60 if pengiriman_obj_wp.waktu_mulai_muat>0 else -1,"status_akhir_pengiriman":pengiriman_obj_wp.status_pengiriman,"biaya_total_trip":pengiriman_obj_wp.biaya_pengiriman_total,"waktu_permintaan_dibuat_jam":pengiriman_obj_wp.waktu_permintaan_dibuat/3600,"waktu_selesai_aktual_jam":pengiriman_obj_wp.waktu_penyelesaian_aktual/3600,"deadline_sla_jam":pengiriman_obj_wp.deadline_penyelesaian/3600})
            
            truk_event.indeks_waypoint_tur_saat_ini+=1; truk_event.waktu_event_selanjutnya=waktu_setelah_aktivitas
            if truk_event.indeks_waypoint_tur_saat_ini>=len(truk_event.tur_konsolidasi_saat_ini):
                truk_event.status="menyelesaikan_tur_s3"
            
            if truk_event.status != "menyelesaikan_tur_s3":
                 events_s3.append((truk_event.waktu_event_selanjutnya, "LANJUT_TUR_S3", truk_event.id_truk))
            
            events_s3.sort()
        
    for p_sisa in _pengiriman_diproses_s3:
        if p_sisa.status_pengiriman in["menunggu_alokasi_truk","dijadwalkan_konsolidasi_s3"]and not p_sisa.is_delivery_completed:p_sisa.status_pengiriman="tidak_terproses_s3_final"
    return _hasil_trip_simulasi_s3,_pengiriman_diproses_s3
# ==== Fungsi Dispatcher Utama ====
def jalankan_simulasi_sistem_logistik(
    jumlah_truk: int, jumlah_pengiriman: int, durasi_simulasi_hari: int, 
    avoid_traffic_api: bool, 
    run_number: int, 
    selected_routing_mode: str, 
    selected_distribusi_mode: str, 
    selected_scenario_str_gui: str, 
    fixed_origin: Optional[str] = None, 
    fixed_destination: Optional[str] = None,
    daftar_kota_depot_str: Optional[str] = None
    ):
    
    # Bagian inisialisasi 
    inisialisasi_sistem_simulasi_global(jumlah_truk, daftar_kota_depot_str=daftar_kota_depot_str)
    generate_permintaan_pengiriman_global(jumlah_pengiriman, durasi_generasi_hari=durasi_simulasi_hari,
                                          mode_pengiriman=selected_distribusi_mode,
                                          fixed_origin_city=fixed_origin,
                                          fixed_destination_city=fixed_destination)
    
    print(f"\nMemulai Simulasi (Run {run_number}) - Skenario GUI: {selected_scenario_str_gui}")
    print(f"  Mode Perutean Aktual: {selected_routing_mode}")

    pengiriman_diproses_final: List[Pengiriman] = []
    hasil_trip_simulasi_final: List[Dict] = [] 

    # Pemilihan skenario 
    if "Skenario 1" in selected_scenario_str_gui:
        hasil_trip_simulasi_final, pengiriman_diproses_final = jalankan_skenario1_rute_tetap_penjadwalan_statis(selected_routing_mode, avoid_traffic_api, run_number)
    elif "Skenario 2" in selected_scenario_str_gui:
        hasil_trip_simulasi_final, pengiriman_diproses_final = jalankan_skenario2_rute_dinamis_penjadwalan_intertruck(avoid_traffic_api, run_number, selected_routing_mode) 
    elif "Skenario 3" in selected_scenario_str_gui:
        hasil_trip_simulasi_final, pengiriman_diproses_final = jalankan_skenario3_konsolidasi_pengiriman(selected_routing_mode, avoid_traffic_api, run_number)
    else: 
        hasil_trip_simulasi_final, pengiriman_diproses_final = jalankan_simulasi_dasar(selected_routing_mode, avoid_traffic_api, run_number)
    
    pengiriman_obj_utk_visualisasi=[p for p in pengiriman_diproses_final if p.status_pengiriman.startswith("selesai")]
    map_file_static,map_file_animated=None,None
    
    # Persiapan Rangkuman 
    shipment_summary = defaultdict(int)
    for p in pengiriman_diproses_final:
        if p.status_pengiriman == "selesai": shipment_summary['tepat_waktu'] += 1
        elif p.status_pengiriman == "selesai_terlambat": shipment_summary['terlambat'] += 1
        else: shipment_summary['gagal'] += 1

    truck_summary = defaultdict(int)
    for t in armada_truk_global:
        if t.jumlah_trip_selesai > 0: truck_summary['beroperasi'] += 1
        else: truck_summary['menganggur'] += 1

    depots_used = list(set(t.lokasi_depot for t in armada_truk_global))
    all_cities_for_map = set(depots_used)
    for p in pengiriman_diproses_final:
        all_cities_for_map.add(p.kota_asal)
        all_cities_for_map.add(p.kota_tujuan)

    # Peta Statis 
    map_file_static = save_route_map_html_multi(pengiriman_diproses_final, run_number, FULL_SAVE_DIRECTORY, depots_to_mark=depots_used, shipment_summary=shipment_summary, truck_summary=truck_summary)

    # === PEMBUATAN PETA DINAMIS ===
    if pengiriman_obj_utk_visualisasi:
        animation_df = prepare_animation_data_multi(pengiriman_obj_utk_visualisasi, ANIMATION_TIME_STEP_MIN)
        if not animation_df.empty:
            
            colors = px.colors.qualitative.Plotly
            max_frame = animation_df['frame_id'].max()
            unique_trucks_anim = sorted(animation_df['legend_anim_label'].unique())
            color_map = {truck: colors[i % len(colors)] for i, truck in enumerate(unique_trucks_anim)}

            fig = go.Figure()
            
            # --- GAMBAR SEMUA ELEMEN STATIS TERLEBIH DAHULU ---
            # 1.A Tambahkan semua jejak rute statis (garis)
            for p_obj in pengiriman_obj_utk_visualisasi:
                color = color_map.get(f"Truk {p_obj.truk_yang_ditugaskan_id[-3:]}", "#CCCCCC")
                # Rute depot ke asal (garis putus-putus)
                if p_obj.rute_depot_ke_asal_json_detail and p_obj.rute_depot_ke_asal_json_detail.get("legs"):
                    points = p_obj.rute_depot_ke_asal_json_detail["legs"][0]["points"]
                    fig.add_trace(go.Scattergeo(lon=[pt["longitude"] for pt in points], lat=[pt["latitude"] for pt in points], mode='lines', line=dict(width=1.5, color=color, dash='dot'), hoverinfo='none', showlegend=False))
                # Rute utama (garis solid)
                if p_obj.rute_json_detail and p_obj.rute_json_detail.get("legs"):
                    points = p_obj.rute_json_detail["legs"][0]["points"]
                    fig.add_trace(go.Scattergeo(lon=[pt["longitude"] for pt in points], lat=[pt["latitude"] for pt in points], mode='lines', line=dict(width=2, color=color), hoverinfo='none', showlegend=False))
                    # Tandai titik asal dan tujuan
                    fig.add_trace(go.Scattergeo(lon=[points[0]["longitude"]], lat=[points[0]["latitude"]], mode='markers', marker=dict(size=8, color=color, symbol='circle'), text=f"Asal: {p_obj.kota_asal}", hoverinfo='text', showlegend=False))
                    fig.add_trace(go.Scattergeo(lon=[points[-1]["longitude"]], lat=[points[-1]["latitude"]], mode='markers', marker=dict(size=8, color=color, symbol='star'), text=f"Tujuan: {p_obj.kota_tujuan}", hoverinfo='text', showlegend=False))
            
            # 1.B Tandai semua lokasi depot
            if depots_used:
                fig.add_trace(go.Scattergeo(lon=[KOTA_KOORDINAT[k][1] for k in depots_used], lat=[KOTA_KOORDINAT[k][0] for k in depots_used], mode='markers', marker=dict(size=10, color='black', symbol='diamond-wide'), name='Lokasi Depot', hoverinfo='text', text=[f"Depot: {k}" for k in depots_used]))

            # BUAT TRACE DINAMIS SECARA EKSPLISIT ---
            # 2.A Tambahkan trace dinamis (titik truk) untuk posisi awal dan SIMPAN INDEKSNYA
            dynamic_trace_indices = []
            for truck_label in unique_trucks_anim:
                df_frame0 = animation_df[(animation_df['frame_id'] == 0) & (animation_df['legend_anim_label'] == truck_label)]
                # Tambahkan trace MESKIPUN kosong di frame 0 agar urutan indeks benar
                fig.add_trace(go.Scattergeo(
                    lon=df_frame0['longitude'], lat=df_frame0['latitude'],
                    mode='markers', marker=dict(color=color_map[truck_label], size=12, line=dict(width=1.5, color='black')),
                    name=truck_label, # Ini akan memunculkan truk di legenda
                    hoverinfo='text', text=df_frame0['hover_text']
                ))
                dynamic_trace_indices.append(len(fig.data) - 1) # Simpan indeks dari trace yang baru ditambahkan

            # 2.B Buat FRAME ANIMASI dengan menargetkan indeks yang benar
            fig.frames = [go.Frame(
                name=str(i),
                # `traces` memberitahu Plotly HANYA trace mana yang akan di-update
                traces=dynamic_trace_indices,
                # `data` sekarang hanya berisi data untuk trace dinamis, urutannya harus sesuai
                data=[
                    go.Scattergeo(
                        lon=animation_df[(animation_df['frame_id'] == i) & (animation_df['legend_anim_label'] == truck_label)]['longitude'],
                        lat=animation_df[(animation_df['frame_id'] == i) & (animation_df['legend_anim_label'] == truck_label)]['latitude'],
                        text=animation_df[(animation_df['frame_id'] == i) & (animation_df['legend_anim_label'] == truck_label)]['hover_text'],
                    ) for truck_label in unique_trucks_anim
                ]
            ) for i in range(int(max_frame) + 1)]

            # Persiapan data untuk panel log dinamis 
            payload_for_js = {
                "shipments": {k: v for k, v in _prepare_animation_events(pengiriman_diproses_final).items()},
                "summary": {
                    "shipments": f"<b>Rangkuman Pengiriman:</b><br>Tepat Waktu: {shipment_summary['tepat_waktu']}<br>Terlambat: {shipment_summary['terlambat']}<br>Gagal: {shipment_summary['gagal']}",
                    "trucks": f"<b>Rangkuman Armada:</b><br>Truk Beroperasi: {truck_summary['beroperasi']}<br>Truk Menganggur: {truck_summary['menganggur']}"
                },
                "max_frame": int(max_frame)
            }
            
            # Konfigurasi layout dan simpan file 
            _configure_animation_layout(fig, max_frame, all_cities_for_map, run_number)
            map_file_animated = save_dynamic_log_map_html(fig, payload_for_js, run_number, FULL_SAVE_DIRECTORY)

    return hasil_trip_simulasi_final, pengiriman_diproses_final, armada_truk_global, map_file_static, map_file_animated

# ==== GUI Lokal Tkinter ====
class SimulasiApp(tk.Tk):
    def __init__(self):
        super().__init__();self.title("Simulasi Sistem Transportasi Truk Nasional");self.geometry("1200x850")
        self.resizable(True,True);self.simulation_run_counter=0;self.default_font=tkFont.nametofont("TkDefaultFont")
        self.default_font.configure(size=10);self.option_add('*Font',self.default_font);self.create_widgets()

    def update_od_combobox_state(self,event=None):
        mode=self.mode_pengiriman_var.get()
        if mode=="Satu Asal ke Satu Tujuan":self.fixed_origin_dropdown.config(state="readonly");self.fixed_destination_dropdown.config(state="readonly")
        elif mode=="Satu Asal ke Banyak Tujuan (Acak)":self.fixed_origin_dropdown.config(state="readonly");self.fixed_destination_dropdown.config(state="disabled");self.fixed_destination_var.set(KOTA_LIST_DROPDOWN_ACAK[0])
        elif mode=="Banyak Asal (Acak) ke Satu Tujuan":self.fixed_origin_dropdown.config(state="disabled");self.fixed_destination_dropdown.config(state="readonly");self.fixed_origin_var.set(KOTA_LIST_DROPDOWN_ACAK[0])
        else:self.fixed_origin_dropdown.config(state="disabled");self.fixed_destination_dropdown.config(state="disabled");self.fixed_origin_var.set(KOTA_LIST_DROPDOWN_ACAK[0]);self.fixed_destination_var.set(KOTA_LIST_DROPDOWN_ACAK[0])

    def update_traffic_for_routing_mode(self,event=None):
        routing_mode=self.routing_mode_var.get()
        if routing_mode=="Model Rute Internal (Non-API)":self.avoid_traffic_var.set(False);self.traffic_checkbutton.config(state="disabled");self.scenario_dropdown.config(state="disabled");self.scenario_var.set("Simulasi Umum")
        else:self.traffic_checkbutton.config(state="normal");self.scenario_dropdown.config(state="readonly");self.update_traffic_checkbox_state()

    def create_widgets(self):
        self.tabControl=ttk.Notebook(self);self.tab1=ttk.Frame(self.tabControl);self.tabControl.add(self.tab1,text='Pengaturan & Kontrol Simulasi')
        settings_frame=ttk.LabelFrame(self.tab1,text="Parameter Simulasi Sistem");settings_frame.pack(padx=10,pady=10,fill=tk.X,expand=True)
        row_idx=0
        ttk.Label(settings_frame,text="Mode Perutean:").grid(row=row_idx,column=0,padx=5,pady=4,sticky=tk.W)
        self.routing_mode_var=tk.StringVar(self);routing_options=["API Mapbox (Default)","Model Rute Internal (Non-API)"];self.routing_mode_dropdown=ttk.Combobox(settings_frame,textvariable=self.routing_mode_var,values=routing_options,width=28,state="readonly")
        self.routing_mode_dropdown.set(routing_options[0]);self.routing_mode_dropdown.grid(row=row_idx,column=1,columnspan=2,padx=5,pady=4,sticky=tk.EW);self.routing_mode_dropdown.bind("<<ComboboxSelected>>",self.update_traffic_for_routing_mode);row_idx+=1
        ttk.Label(settings_frame,text="Jumlah Truk:").grid(row=row_idx,column=0,padx=5,pady=4,sticky=tk.W)
        self.jumlah_truk_entry=ttk.Entry(settings_frame,width=8);self.jumlah_truk_entry.insert(0,str(JUMLAH_TRUK_DEFAULT));self.jumlah_truk_entry.grid(row=row_idx,column=1,padx=5,pady=4,sticky=tk.EW)
        ttk.Label(settings_frame,text="Jumlah Pengiriman:").grid(row=row_idx,column=2,padx=5,pady=4,sticky=tk.W)
        self.jumlah_pengiriman_entry=ttk.Entry(settings_frame,width=8);self.jumlah_pengiriman_entry.insert(0,str(JUMLAH_PENGIRIMAN_DEFAULT));self.jumlah_pengiriman_entry.grid(row=row_idx,column=3,padx=5,pady=4,sticky=tk.EW)
        ttk.Label(settings_frame,text="Durasi Permintaan (hari):").grid(row=row_idx,column=4,padx=5,pady=4,sticky=tk.W)
        self.durasi_simulasi_entry=ttk.Entry(settings_frame,width=8);self.durasi_simulasi_entry.insert(0,"1");self.durasi_simulasi_entry.grid(row=row_idx,column=5,padx=5,pady=4,sticky=tk.EW);row_idx+=1
        ttk.Label(settings_frame,text="Distribusi Pengiriman:").grid(row=row_idx,column=0,padx=5,pady=4,sticky=tk.W)
        self.mode_pengiriman_var=tk.StringVar(self);modes=["Acak ke Acak","Satu Asal ke Satu Tujuan","Satu Asal ke Banyak Tujuan (Acak)","Banyak Asal (Acak) ke Satu Tujuan"]
        self.mode_pengiriman_dropdown=ttk.Combobox(settings_frame,textvariable=self.mode_pengiriman_var,values=modes,width=28,state="readonly");self.mode_pengiriman_dropdown.set(modes[0])
        self.mode_pengiriman_dropdown.grid(row=row_idx,column=1,columnspan=2,padx=5,pady=4,sticky=tk.EW);self.mode_pengiriman_dropdown.bind("<<ComboboxSelected>>",self.update_od_combobox_state);row_idx+=1
        ttk.Label(settings_frame,text="Kota Asal Tetap:").grid(row=row_idx,column=0,padx=5,pady=4,sticky=tk.W)
        self.fixed_origin_var=tk.StringVar(self);self.fixed_origin_dropdown=ttk.Combobox(settings_frame,textvariable=self.fixed_origin_var,values=KOTA_LIST_DROPDOWN_ACAK,width=18,state="disabled")
        self.fixed_origin_dropdown.set(KOTA_LIST_DROPDOWN_ACAK[0]);self.fixed_origin_dropdown.grid(row=row_idx,column=1,padx=5,pady=4,sticky=tk.EW)
        ttk.Label(settings_frame,text="Kota Tujuan Tetap:").grid(row=row_idx,column=2,padx=5,pady=4,sticky=tk.W)
        self.fixed_destination_var=tk.StringVar(self);self.fixed_destination_dropdown=ttk.Combobox(settings_frame,textvariable=self.fixed_destination_var,values=KOTA_LIST_DROPDOWN_ACAK,width=18,state="disabled")
        self.fixed_destination_dropdown.set(KOTA_LIST_DROPDOWN_ACAK[0]);self.fixed_destination_dropdown.grid(row=row_idx,column=3,padx=5,pady=4,sticky=tk.EW);row_idx+=1
        ttk.Label(settings_frame,text="Skenario Studi Kasus:").grid(row=row_idx,column=0,padx=5,pady=4,sticky=tk.W)
        self.scenario_var=tk.StringVar(self);scenarios=["Simulasi Umum","Skenario 1 (Rute Tetap & Statis)","Skenario 2 (Rute Dinamis & Inter-Truck)","Skenario 3 (Pengiriman Gabungan)","Skenario 4 (Infrastruktur Depot)"]
        self.scenario_dropdown=ttk.Combobox(settings_frame,textvariable=self.scenario_var,values=scenarios,width=35,state="readonly");self.scenario_dropdown.set(scenarios[0])
        self.scenario_dropdown.grid(row=row_idx,column=1,columnspan=3,padx=5,pady=4,sticky=tk.EW)
        self.avoid_traffic_var=tk.BooleanVar(value=True);self.traffic_checkbutton=ttk.Checkbutton(settings_frame,text="Gunakan Lalu Lintas Real-time (API)",variable=self.avoid_traffic_var)
        self.traffic_checkbutton.grid(row=row_idx,column=4,columnspan=2,padx=5,pady=4,sticky=tk.W);self.scenario_dropdown.bind("<<ComboboxSelected>>",self.update_traffic_checkbox_state);row_idx+=1
        ttk.Label(settings_frame,text="Kota Depot (koma: Bali,Jakarta):").grid(row=row_idx,column=0,columnspan=2,padx=5,pady=4,sticky=tk.W)
        self.depot_cities_entry=ttk.Entry(settings_frame,width=40);self.depot_cities_entry.grid(row=row_idx,column=2,columnspan=4,padx=5,pady=4,sticky=tk.EW);row_idx+=1
        self.run_button=ttk.Button(settings_frame,text="Mulai Simulasi Sistem",command=self.start_simulation_thread,style="Accent.TButton");self.run_button.grid(row=row_idx,column=0,columnspan=6,pady=15,padx=5,sticky=tk.EW)
        for i in range(6):settings_frame.columnconfigure(i,weight=1)
        self.tab_output=ttk.Frame(self.tabControl);self.tabControl.add(self.tab_output,text='Output & Log Simulasi')
        self.output_text=tk.Text(self.tab_output,height=30,width=100,wrap=tk.WORD,font=('Courier New',10));self.output_text.pack(pady=10,padx=10,fill=tk.BOTH,expand=True)
        self.scrollbar=ttk.Scrollbar(self.output_text,command=self.output_text.yview);self.scrollbar.pack(side=tk.RIGHT,fill=tk.Y);self.output_text.config(yscrollcommand=self.scrollbar.set)
        self.tabControl.pack(expand=1,fill="both",padx=5,pady=5);self.update_od_combobox_state();self.update_traffic_checkbox_state();self.update_traffic_for_routing_mode()

    def update_traffic_checkbox_state(self,event=None):
        selected_scenario=self.scenario_var.get();routing_mode=self.routing_mode_var.get()
        if routing_mode=="API Mapbox (Default)":
            self.traffic_checkbutton.config(state="normal")
            if "Skenario 1" in selected_scenario:self.avoid_traffic_var.set(False);self.traffic_checkbutton.config(state="disabled")
            elif "Skenario 2" in selected_scenario:self.avoid_traffic_var.set(True);self.traffic_checkbutton.config(state="disabled")
        else:self.avoid_traffic_var.set(False);self.traffic_checkbutton.config(state="disabled")

    def _open_map_safely(self, map_file_path, map_type_name="peta"):
        if map_file_path and os.path.exists(map_file_path):
            log_message = f"Peta {map_type_name} telah dibuat dan disimpan di:\n{map_file_path}\n"
            self.output_text.insert(tk.END, "\n" + log_message)
            try:
                webbrowser.open(f"file:///{os.path.realpath(map_file_path)}")
            except Exception as e:
                print(f"Gagal membuka browser secara otomatis: {e}")
            return True
        else:
            log_message_error = f"File {map_type_name} tidak ditemukan atau gagal dibuat: {map_file_path}"
            self.output_text.insert(tk.END, "\n" + log_message_error)
        return False
    
    def start_simulation_thread(self):
        """Fungsi ini dipanggil oleh tombol GUI untuk memulai thread simulasi."""
        self.run_button.config(state="disabled", text="Simulasi sedang berjalan...")
        self.output_text.delete("1.0", tk.END)
        self.output_text.insert(tk.END, "Mempersiapkan thread untuk simulasi...\n")
        
        sim_thread = threading.Thread(target=self.run_simulation_worker)
        sim_thread.daemon = True
        sim_thread.start()

    def run_simulation_worker(self):
        """Fungsi ini menjalankan simulasi di thread terpisah untuk mencegah GUI freeze/crash."""
        try:
            jumlah_truk = int(self.jumlah_truk_entry.get())
            jumlah_pengiriman = int(self.jumlah_pengiriman_entry.get())
            durasi_simulasi = int(self.durasi_simulasi_entry.get())
            if jumlah_truk <= 0 or jumlah_pengiriman <= 0 or durasi_simulasi <= 0:
                raise ValueError("Jumlah & durasi harus lebih besar dari 0.")
            
            routing_mode_val = self.routing_mode_var.get()
            mode_pengiriman_val = self.mode_pengiriman_var.get()
            fixed_origin_val = self.fixed_origin_var.get()
            selected_fixed_origin = fixed_origin_val if fixed_origin_val != KOTA_LIST_DROPDOWN_ACAK[0] and self.fixed_origin_dropdown["state"] != "disabled" else None
            fixed_dest_val = self.fixed_destination_var.get()
            selected_fixed_destination = fixed_dest_val if fixed_dest_val != KOTA_LIST_DROPDOWN_ACAK[0] and self.fixed_destination_dropdown["state"] != "disabled" else None
            
            if mode_pengiriman_val == "Satu Asal ke Satu Tujuan" and (not selected_fixed_origin or not selected_fixed_destination or selected_fixed_origin == selected_fixed_destination):
                raise ValueError("Mode 'Satu Asal ke Satu Tujuan' perlu Asal & Tujuan valid & beda.")
            if mode_pengiriman_val == "Satu Asal ke Banyak Tujuan (Acak)" and not selected_fixed_origin:
                raise ValueError("Mode 'Satu Asal ke Banyak Tujuan' perlu Asal Tetap valid.")
            if mode_pengiriman_val == "Banyak Asal (Acak) ke Satu Tujuan" and not selected_fixed_destination:
                raise ValueError("Mode 'Banyak Asal ke Satu Tujuan' perlu Tujuan Tetap valid.")
            
            self.simulation_run_counter += 1
            selected_scenario_str_gui = self.scenario_var.get()
            avoid_traffic_final_val = self.avoid_traffic_var.get()
            daftar_kota_depot_input = self.depot_cities_entry.get()

            hasil_trips, pengiriman_diproses_final, status_armada_akhir, map_file_s, map_file_a = \
                jalankan_simulasi_sistem_logistik(jumlah_truk, jumlah_pengiriman, durasi_simulasi, avoid_traffic_final_val, 
                                                  self.simulation_run_counter, routing_mode_val, mode_pengiriman_val, 
                                                  selected_scenario_str_gui, selected_fixed_origin, selected_fixed_destination, 
                                                  daftar_kota_depot_input)

            self.after(0, self.simulation_finished, hasil_trips, pengiriman_diproses_final, status_armada_akhir, map_file_s, map_file_a, selected_scenario_str_gui)

        except Exception as e:
            self.after(0, self.simulation_error, e)

    def simulation_finished(self, hasil_trips, pengiriman_diproses_final, status_armada_akhir, map_file_s, map_file_a, scenario_name_display):
        """Dipanggil di main thread setelah simulasi berhasil untuk menampilkan output."""
        self.output_text.insert(tk.END, "\n" + "="*80 + "\n")
        self.output_text.insert(tk.END, " " * 28 + "HASIL AKHIR SIMULASI\n")
        self.output_text.insert(tk.END, "="*80 + "\n\n")

        # --- Formula Perhitungan Biaya ---
        self.output_text.insert(tk.END, "--- Formula & Variabel Perhitungan Biaya Operasional ---\n")
        self.output_text.insert(tk.END, f"  - Tarif BBM per Liter       : Rp{TARIF_BBM:,.0f}\n")
        self.output_text.insert(tk.END, f"  - Gaji Sopir per Jam        : Rp{GAJI_SOPIR_PER_JAM:,.0f}\n")
        self.output_text.insert(tk.END, f"  - Biaya Pemeliharaan per Trip: Rp{BIAYA_PEMELIHARAAN_PER_TRIP:,.0f}\n")
        self.output_text.insert(tk.END, f"  - Konsumsi BBM (Asumsi)     : Antara {MIN_KONSUMSI_BBM_UNIFORM} dan {MAX_KONSUMSI_BBM_UNIFORM} Liter/Jam\n")
        self.output_text.insert(tk.END, "  - Fungsi Biaya Perjalanan   : (Waktu Tempuh Jam * Gaji) + (Waktu Tempuh Jam * Konsumsi BBM * Tarif BBM)\n")
        self.output_text.insert(tk.END, "  - Fungsi Biaya Total Trip   : Biaya Perjalanan + Biaya Pemeliharaan\n\n")

        # --- Rangkuman Per Pengiriman ---
        self.output_text.insert(tk.END, "--- Rangkuman Detail per Pengiriman (yang Berhasil Diproses) ---\n")
        pengiriman_berhasil = [p for p in pengiriman_diproses_final if p.status_pengiriman.startswith("selesai")]
        if not pengiriman_berhasil:
            self.output_text.insert(tk.END, "  Tidak ada pengiriman yang berhasil diselesaikan.\n\n")
        else:
            for p in pengiriman_berhasil: # Ini adalah loop yang Anda maksud
                # Hitung metrik per pengiriman
                waktu_tunggu_alokasi_menit = (p.waktu_truk_dialokasikan - p.waktu_permintaan_dibuat) / 60 if p.waktu_truk_dialokasikan > 0 else 0

                jarak_ke_lokasi_muat_km = 0
                waktu_ke_lokasi_muat_menit = 0
                if p.rute_depot_ke_asal_json_detail and "summary" in p.rute_depot_ke_asal_json_detail:
                    jarak_ke_lokasi_muat_km = p.rute_depot_ke_asal_json_detail["summary"]["lengthInMeters"] / 1000
                    waktu_ke_lokasi_muat_menit = p.rute_depot_ke_asal_json_detail["summary"]["travelTimeInSeconds"] / 60

                waktu_muat_menit = p.estimasi_waktu_pengambilan_barang_menit
                waktu_tempuh_utama_menit = p.estimasi_waktu_tempuh_menit # Sudah ada di objek Pengiriman
                waktu_bongkar_menit = p.estimasi_waktu_bongkar_menit
                total_siklus_menit = (p.waktu_penyelesaian_aktual - p.waktu_permintaan_dibuat) / 60 if p.waktu_penyelesaian_aktual > 0 else 0
                
                # Tampilkan detail untuk PENGIRIMAN SAAT INI (p)
                self.output_text.insert(tk.END, f"  - ID: {p.id_pengiriman} | Truk: {p.truk_yang_ditugaskan_id} | Rute: {p.kota_asal} -> {p.kota_tujuan}\n")
                self.output_text.insert(tk.END, f"    Status      : {p.status_pengiriman.replace('_', ' ').title()}\n")
                self.output_text.insert(tk.END, f"    Jarak Utama : {p.jarak_tempuh_km:.2f} km\n")
                self.output_text.insert(tk.END, f"    Total Biaya : Rp{p.biaya_pengiriman_total:,.0f}\n")
                self.output_text.insert(tk.END,  "    Detail Waktu:\n")
                self.output_text.insert(tk.END, f"      - Waktu Tunggu Alokasi    : {waktu_tunggu_alokasi_menit:6.1f} menit\n")
                self.output_text.insert(tk.END, f"      - Perjalanan ke Lokasi Muat : {waktu_ke_lokasi_muat_menit:6.1f} menit ({jarak_ke_lokasi_muat_km:.2f} km)\n") # Ditambahkan jarak
                self.output_text.insert(tk.END, f"      - Proses Muat Barang        : {waktu_muat_menit:6.1f} menit\n")
                self.output_text.insert(tk.END, f"      - Waktu Tempuh Utama        : {waktu_tempuh_utama_menit:6.1f} menit\n")
                self.output_text.insert(tk.END, f"      - Proses Bongkar Barang     : {waktu_bongkar_menit:6.1f} menit\n")
                self.output_text.insert(tk.END,  "      -------------------------------------------- +\n")
                self.output_text.insert(tk.END, f"      => Total Waktu Siklus       : {total_siklus_menit:6.1f} menit ({total_siklus_menit/60:.2f} jam)\n")
                self.output_text.insert(tk.END, f"    Target SLA                  : {p.target_waktu_penyelesaian_sla_menit:6.1f} menit ({p.target_waktu_penyelesaian_sla_menit/60:.2f} jam)\n")
                self.output_text.insert(tk.END, f"    Status SLA                  : {'Terlambat' if p.status_pengiriman == 'selesai_terlambat' else 'Tepat Waktu'}\n\n") # Tambahkan status SLA eksplisit
        # --- Rangkuman Per Armada ---
        # ... (sisanya dari kode Anda)    # --- Rangkuman Per Armada ---
        self.output_text.insert(tk.END, "--- Rangkuman Detail per Armada (yang Beroperasi) ---\n")
        armada_beroperasi = [t for t in status_armada_akhir if t.jumlah_trip_selesai > 0]
        if not armada_beroperasi:
            self.output_text.insert(tk.END, "  Tidak ada truk yang beroperasi.\n\n")
        else:
            for t in armada_beroperasi:
                total_biaya_truk = t.total_biaya_bbm + t.total_biaya_sopir + t.total_biaya_pemeliharaan
                self.output_text.insert(tk.END, f"  - Truk ID   : {t.id_truk} (Depot: {t.lokasi_depot})\n")
                self.output_text.insert(tk.END, f"    Trip Selesai: {t.jumlah_trip_selesai}\n")
                self.output_text.insert(tk.END, f"    Total Jarak : {t.total_km_operasional:.2f} km\n")
                self.output_text.insert(tk.END, f"    Total Mengemudi: {t.total_jam_operasional_mengemudi:.2f} jam\n")
                self.output_text.insert(tk.END, f"    Total Biaya : Rp{total_biaya_truk:,.0f}\n\n")

        # --- Rangkuman Keseluruhan ---
        self.output_text.insert(tk.END, "--- Rangkuman Kinerja Keseluruhan ---\n")
        shipment_summary = defaultdict(int)
        for p in pengiriman_diproses_final:
            if p.status_pengiriman == "selesai": shipment_summary['tepat_waktu'] += 1
            elif p.status_pengiriman == "selesai_terlambat": shipment_summary['terlambat'] += 1
            else: shipment_summary['gagal'] += 1
        
        total_biaya_operasional = sum(t.total_biaya_bbm + t.total_biaya_sopir + t.total_biaya_pemeliharaan for t in status_armada_akhir)

        self.output_text.insert(tk.END, f"  - Pengiriman Tepat Waktu: {shipment_summary['tepat_waktu']} / {len(pengiriman_diproses_final)}\n")
        self.output_text.insert(tk.END, f"  - Pengiriman Terlambat  : {shipment_summary['terlambat']} / {len(pengiriman_diproses_final)}\n")
        self.output_text.insert(tk.END, f"  - Pengiriman Gagal      : {shipment_summary['gagal']} / {len(pengiriman_diproses_final)}\n")
        self.output_text.insert(tk.END, f"  - Total Keseluruhan Biaya Operasional: Rp{total_biaya_operasional:,.0f}\n\n")
        
        self.update_idletasks()
        self._open_map_safely(map_file_s, "statis")
        self._open_map_safely(map_file_a, "animasi")
        
        messagebox.showinfo("Simulasi Selesai", f"{scenario_name_display} (Run {self.simulation_run_counter}) selesai.\nFile peta disimpan di:\n{FULL_SAVE_DIRECTORY}")
        self.run_button.config(state="normal", text="Mulai Simulasi Sistem")
    def simulation_error(self, error):
        """Dipanggil di main thread jika terjadi error saat simulasi."""
        self.output_text.insert(tk.END, f"\n\nERROR SIMULASI UTAMA: {error}\n")
        self.output_text.insert(tk.END, traceback.format_exc())
        messagebox.showerror("Error Simulasi", f"Terjadi error saat menjalankan simulasi:\n{error}")
        self.run_button.config(state="normal", text="Mulai Simulasi Sistem")

if __name__=="__main__":
    app=SimulasiApp()
    style=ttk.Style(app);available_themes=style.theme_names()
    if 'clam' in available_themes:style.theme_use('clam')
    elif 'vista' in available_themes:style.theme_use('vista')
    style.configure("Accent.TButton",foreground="white",background="#0078D4",font=('Segoe UI',10,'bold'))
    style.map("Accent.TButton",background=[('active','#005A9E')])
    app.mainloop()