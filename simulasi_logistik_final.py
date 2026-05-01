"""
=============================================================================
SIMULASI SISTEM LOGISTIK TRANSPORTASI TRUK NASIONAL
Versi 4.0 — Refactored, PEP 8 & Pylint Compliant

Deskripsi:
    Simulasi berbasis event discrete untuk sistem pengiriman barang
    menggunakan armada truk antar kota di Indonesia.

    Mendukung 4 mode simulasi:
    - Simulasi Umum     : Alokasi truk tersedia pertama kali
    - Skenario 1        : Rute tetap & penjadwalan statis
    - Skenario 2        : Rute dinamis & alokasi inter-truk
    - Skenario 3        : Konsolidasi pengiriman (tur gabungan)
=============================================================================
"""

import math
import os
import json
import random
import threading
import traceback
import webbrowser
from collections import defaultdict
from typing import Dict, List, Optional, Tuple

import numpy as np
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
import requests
import tkinter as tk
from tkinter import font as tkFont
from tkinter import messagebox
from tkinter import ttk


# =============================================================================
# BAGIAN 1 — KONSTANTA KONFIGURASI
# =============================================================================

KUNCI_API_MAPBOX: str = "MASUKKAN API MAPBOX ANDA DISNI"  # Ganti dengan token Mapbox valid

# Tarif biaya operasional (dalam Rupiah)
TARIF_BBM: int = 13_000
GAJI_SOPIR_PER_JAM: int = 30_000
BIAYA_PEMELIHARAAN_PER_TRIP: int = 100_000

# Nilai default antarmuka
JUMLAH_TRUK_DEFAULT: int = 3
JUMLAH_PENGIRIMAN_DEFAULT: int = 4
LANGKAH_WAKTU_ANIMASI_MENIT: int = 60

# Parameter distribusi stokastik
LAMBDA_JUMLAH_BARANG: int = 10
RATA_RATA_WAKTU_MUAT_MENIT: int = 15
SIMPANGAN_WAKTU_MUAT_MENIT: int = 5
RATA_RATA_SLA_MENIT: int = 240
SIMPANGAN_SLA_MENIT: int = 30
MIN_KONSUMSI_BBM_LITER_PER_JAM: int = 3
MAKS_KONSUMSI_BBM_LITER_PER_JAM: int = 6
WAKTU_TEMPUH_INTERNAL_MIN_MENIT: int = 30
WAKTU_TEMPUH_INTERNAL_MODE_MENIT: int = 60
WAKTU_TEMPUH_INTERNAL_MAKS_MENIT: int = 120

# Direktori penyimpanan file output
DIREKTORI_RUMAH: str = os.path.expanduser("~")
DIREKTORI_DOKUMEN: str = os.path.join(DIREKTORI_RUMAH, "Documents")
NAMA_FOLDER_SIMPAN: str = "simulasi_maps_logistik_final"
DIREKTORI_SIMPAN: str = os.path.join(DIREKTORI_DOKUMEN, NAMA_FOLDER_SIMPAN)
os.makedirs(DIREKTORI_SIMPAN, exist_ok=True)

# Koordinat kota: (lintang, bujur, wilayah_pulau)
KOTA_KOORDINAT: Dict[str, Tuple[float, float, str]] = {
    "Jakarta":    (-6.200000,  106.816666, "Jawa"),
    "Bandung":    (-6.914864,  107.608238, "Jawa"),
    "Surabaya":   (-7.257472,  112.752088, "Jawa"),
    "Semarang":   (-6.966667,  110.416664, "Jawa"),
    "Yogyakarta": (-7.795580,  110.369490, "Jawa"),
    "Medan":      ( 3.595196,   98.672226, "Sumatra"),
    "Palembang":  (-2.976074,  104.775429, "Sumatra"),
    "Makassar":   (-5.147665,  119.432732, "Sulawesi"),
    "Denpasar":   (-8.670458,  115.212629, "Bali"),
    "Pekanbaru":  ( 0.507068,  101.447777, "Sumatra"),
    "Padang":     (-0.947083,  100.350601, "Sumatra"),
    "Balikpapan": (-1.237927,  116.852852, "Kalimantan"),
    "Manado":     ( 1.474830,  124.842079, "Sulawesi"),
    "Pontianak":  (-0.027392,  109.333931, "Kalimantan"),
    "Banjarmasin":(-3.316694,  114.590111, "Kalimantan"),
    "Kupang":     (-10.175000, 123.600000, "Nusa Tenggara"),
}

DAFTAR_KOTA_DROPDOWN: List[str] = (
    ["(Pilih Kota)"] + sorted(list(KOTA_KOORDINAT.keys()))
)
DAFTAR_KOTA_DROPDOWN_ACAK: List[str] = (
    ["(Acak)"] + sorted(list(KOTA_KOORDINAT.keys()))
)

BATAS_WILAYAH: Dict[str, Dict[str, List[float]]] = {
    "Jawa":      {"lat": [-8.9, -5.9], "lon": [105.0, 114.7]},
    "Sumatra":   {"lat": [-6.0,  6.0], "lon": [ 95.0, 106.0]},
    "Indonesia": {"lat": [-11.0, 6.0], "lon": [ 95.0, 141.0]},
}


# =============================================================================
# BAGIAN 2 — KELAS ENTITAS SIMULASI
# =============================================================================

class Pengiriman:
    """
    Merepresentasikan satu permintaan pengiriman barang dari kota asal
    ke kota tujuan, beserta seluruh atribut waktu, biaya, dan status-nya.
    """

    penghitung_id: int = 0

    def __init__(
        self,
        kota_asal: str,
        kota_tujuan: str,
        waktu_permintaan_dibuat: float,
        id_pengiriman: Optional[str] = None,
    ):
        if id_pengiriman is None:
            Pengiriman.penghitung_id += 1
            self.id_pengiriman = f"P{Pengiriman.penghitung_id:04d}"
        else:
            self.id_pengiriman = id_pengiriman

        if kota_asal not in KOTA_KOORDINAT or kota_tujuan not in KOTA_KOORDINAT:
            raise ValueError(
                f"Kota asal ({kota_asal}) atau tujuan ({kota_tujuan}) tidak valid."
            )

        self.kota_asal: str = kota_asal
        self.kota_tujuan: str = kota_tujuan
        self.jumlah_barang_ton: float = max(
            1, np.random.poisson(lam=LAMBDA_JUMLAH_BARANG)
        )
        self.waktu_permintaan_dibuat: float = waktu_permintaan_dibuat

        self.target_sla_menit: float = max(
            1,
            np.random.normal(loc=RATA_RATA_SLA_MENIT, scale=SIMPANGAN_SLA_MENIT),
        )
        self.batas_waktu_penyelesaian: float = (
            waktu_permintaan_dibuat + (self.target_sla_menit * 60)
        )

        self.estimasi_waktu_muat_menit: float = max(
            1,
            np.random.normal(
                loc=RATA_RATA_WAKTU_MUAT_MENIT, scale=SIMPANGAN_WAKTU_MUAT_MENIT
            ),
        )
        self.estimasi_waktu_bongkar_menit: float = self.estimasi_waktu_muat_menit
        self.estimasi_waktu_tempuh_menit: float = -1
        self.jarak_tempuh_km: float = -1

        # Waktu-waktu kejadian (diisi selama simulasi)
        self.waktu_truk_dialokasikan: float = -1
        self.waktu_mulai_muat: float = -1
        self.waktu_selesai_muat: float = -1
        self.waktu_keberangkatan: float = -1
        self.waktu_tiba_tujuan: float = -1
        self.waktu_mulai_bongkar: float = -1
        self.waktu_selesai_bongkar: float = -1
        self.waktu_penyelesaian_aktual: float = -1

        # Status dan relasi
        self.status_pengiriman: str = "menunggu_alokasi_truk"
        self.id_truk_ditugaskan: Optional[str] = None
        self.biaya_pengiriman_total: float = 0.0

        # Data rute (diisi saat rute dihitung)
        self.rute_utama_json: Optional[Dict] = None
        self.rute_depot_ke_asal_json: Optional[Dict] = None

        # Atribut untuk skenario konsolidasi (Skenario 3)
        self.urutan_dalam_tur: Optional[int] = None
        self.muat_selesai: bool = False
        self.bongkar_selesai: bool = False

    def __repr__(self) -> str:
        return (
            f"Pengiriman(ID={self.id_pengiriman}, "
            f"{self.kota_asal}→{self.kota_tujuan}, "
            f"{self.jumlah_barang_ton:.1f}T, "
            f"Status={self.status_pengiriman})"
        )


class Truk:
    """
    Merepresentasikan satu unit truk dalam armada, beserta kapasitas,
    lokasi, status operasional, dan akumulasi metrik kinerjanya.
    """

    penghitung_id: int = 0

    def __init__(
        self,
        kapasitas_ton: float,
        lokasi_depot: str,
        id_truk: Optional[str] = None,
    ):
        if id_truk is None:
            Truk.penghitung_id += 1
            self.id_truk = f"T{Truk.penghitung_id:03d}"
        else:
            self.id_truk = id_truk

        if lokasi_depot not in KOTA_KOORDINAT:
            raise ValueError(f"Lokasi depot ({lokasi_depot}) tidak valid.")

        self.kapasitas_ton: float = kapasitas_ton
        #LogikaNOTE 1 & 2:
        # Menentukan jenis dan tarif berdasarkan kapasitas
        if self.kapasitas_ton <= 5.0:
            self.jenis_truk = "CDE"
            self.tarif_per_km = 5000.0
        elif self.kapasitas_ton <= 10.0:
            self.jenis_truk = "CDD"
            self.tarif_per_km = 8000.0
        elif self.kapasitas_ton <= 15.0:
            self.jenis_truk = "FUSO"
            self.tarif_per_km = 12000.0
        else:
            self.jenis_truk = "TRONTON"
            self.tarif_per_km = 16000.0
        self.lokasi_depot: str = lokasi_depot
        self.lokasi_sekarang: str = lokasi_depot
        self.koordinat_sekarang: Tuple[float, float] = (
            KOTA_KOORDINAT[lokasi_depot][0],
            KOTA_KOORDINAT[lokasi_depot][1],
        )

        self.status: str = "siaga_di_depot"
        self.muatan_saat_ini_ton: float = 0.0
        self.waktu_event_berikutnya: float = 0.0
        self.id_pengiriman_aktif: Optional[str] = None

        # Jadwal & tur (untuk Skenario 1 dan 3)
        self.jadwal_tugas_statis: List[Pengiriman] = []
        self.indeks_tugas_statis: int = 0
        self.tur_konsolidasi: List[Tuple["Pengiriman", str]] = []
        self.indeks_waypoint_tur: int = 0
        self.destinasi_berikutnya: Optional[str] = None

        # Akumulasi metrik kinerja
        self.total_km_operasional: float = 0.0
        self.total_jam_mengemudi: float = 0.0
        self.total_jam_memuat: float = 0.0
        self.total_jam_membongkar: float = 0.0
        self.total_biaya_bbm: float = 0.0
        self.total_biaya_sopir: float = 0.0
        self.total_biaya_pemeliharaan: float = 0.0
        self.jumlah_trip_selesai: int = 0

    def __repr__(self) -> str:
        return (
            f"Truk(ID={self.id_truk}, "
            f"Kapasitas={self.kapasitas_ton:.1f}T, "
            f"Lokasi={self.lokasi_sekarang}, "
            f"Status={self.status}, "
            f"Muatan={self.muatan_saat_ini_ton:.1f}T)"
        )

    def apakah_siaga(self, waktu_simulasi: float) -> bool:
        """Mengembalikan True jika truk siaga dan sudah waktunya menerima tugas."""
        status_siaga = self.status in [
            "siaga_di_depot",
            "siaga_setelah_bongkar",
            "siaga_setelah_tur",
        ]
        return status_siaga and self.waktu_event_berikutnya <= waktu_simulasi

    def bisa_angkut(self, berat_ton: float) -> bool:
        """Mengembalikan True jika muatan saat ini + berat baru tidak melebihi kapasitas."""
        return (self.muatan_saat_ini_ton + berat_ton) <= self.kapasitas_ton


# =============================================================================
# BAGIAN 3 — LAYANAN RUTE (Kalkulasi & API)
# =============================================================================

class LayananRute:
    """
    Menyediakan semua fungsi terkait kalkulasi dan pengambilan data rute,
    baik dari API Mapbox maupun model estimasi internal.
    """

    @staticmethod
    def hitung_jarak_haversine(
        lat1: float, lon1: float, lat2: float, lon2: float
    ) -> float:
        """Menghitung jarak (km) antara dua titik koordinat menggunakan formula Haversine."""
        radius_bumi_km = 6371
        lat1_r, lon1_r, lat2_r, lon2_r = map(
            math.radians, [lat1, lon1, lat2, lon2]
        )
        delta_lat = lat2_r - lat1_r
        delta_lon = lon2_r - lon1_r
        a = (
            math.sin(delta_lat / 2) ** 2
            + math.cos(lat1_r) * math.cos(lat2_r) * math.sin(delta_lon / 2) ** 2
        )
        c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
        return radius_bumi_km * c

    @staticmethod
    def dekode_polyline(string_polyline: str) -> List[Dict[str, float]]:
        """Mendekode string polyline terenkripsi menjadi daftar koordinat lintang-bujur."""
        index = 0
        lat = 0
        lng = 0
        koordinat: List[Dict[str, float]] = []
        perubahan = {"lintang": 0, "bujur": 0}

        while index < len(string_polyline):
            for dimensi in ["lintang", "bujur"]:
                geser = 0
                hasil = 0
                while True:
                    if index >= len(string_polyline):
                        raise ValueError("String polyline tidak valid: terpotong tiba-tiba.")
                    byte = ord(string_polyline[index]) - 63
                    index += 1
                    hasil |= (byte & 0x1F) << geser
                    geser += 5
                    if byte < 0x20:
                        break
                if hasil & 1:
                    perubahan[dimensi] = ~(hasil >> 1)
                else:
                    perubahan[dimensi] = hasil >> 1

            lat += perubahan["lintang"]
            lng += perubahan["bujur"]
            koordinat.append({"latitude": lat / 1e5, "longitude": lng / 1e5})

        return koordinat

    @staticmethod
    def ambil_data_rute_mapbox(
        coord_asal: Tuple[float, float],
        coord_tujuan: Tuple[float, float],
        hindari_lalu_lintas: bool = True,
    ) -> Optional[Dict]:
        """
        Mengambil data rute dari API Mapbox Directions.
        Mengembalikan dict ringkasan rute, atau None jika gagal.
        """
        kunci_tidak_valid = (
            not KUNCI_API_MAPBOX
            or KUNCI_API_MAPBOX == "ISI TOKEN DISINI"
        )
        if kunci_tidak_valid:
            print("PERINGATAN: Kunci API Mapbox belum diatur.")
            return None

        string_koordinat = (
            f"{coord_asal[1]},{coord_asal[0]};"
            f"{coord_tujuan[1]},{coord_tujuan[0]}"
        )
        profil = "mapbox/driving-traffic" if hindari_lalu_lintas else "mapbox/driving"
        url = f"https://api.mapbox.com/directions/v5/{profil}/{string_koordinat}"
        parameter = {
            "access_token": KUNCI_API_MAPBOX,
            "geometries": "polyline",
            "overview": "full",
            "steps": "false",
            "alternatives": "false",
        }

        try:
            respons = requests.get(url, params=parameter, timeout=15)
            respons.raise_for_status()
            data = respons.json()

            if data.get("code") != "Ok" or not data.get("routes"):
                print(
                    f"Error Mapbox API: {data.get('code')} - "
                    f"{data.get('message', 'Rute tidak ditemukan')}"
                )
                return None

            rute = data["routes"][0]
            if not rute.get("geometry"):
                print(f"Error Mapbox: Rute ada namun data geometri kosong.")
                return None

            jarak_meter = rute["distance"]
            durasi_detik = rute["duration"]
            titik_titik = LayananRute.dekode_polyline(rute["geometry"])

            return {
                "summary": {
                    "lengthInMeters": jarak_meter,
                    "travelTimeInSeconds": durasi_detik,
                    "trafficDelayInSeconds": 0,
                    "noTrafficTravelTimeInSeconds": durasi_detik,
                },
                "legs": [
                    {
                        "summary": {
                            "lengthInMeters": jarak_meter,
                            "travelTimeInSeconds": durasi_detik,
                        },
                        "points": titik_titik,
                    }
                ],
            }

        except requests.exceptions.Timeout:
            print("Error API Mapbox: Timeout.")
            return None
        except requests.exceptions.HTTPError as err:
            print(
                f"Error API Mapbox: HTTP {err.response.status_code} "
                f"- {err.response.text}"
            )
            return None
        except requests.exceptions.RequestException as err:
            print(f"Error API Mapbox: {err}")
            return None
        except Exception:  # pylint: disable=broad-except
            print(f"Error tidak terduga saat memproses respons Mapbox:")
            print(traceback.format_exc())
            return None

    @staticmethod
    def estimasi_rute_internal(
        coord_asal: Tuple[float, float],
        coord_tujuan: Tuple[float, float],
    ) -> Dict:
        """
        Mengestimasi rute tanpa API menggunakan jarak Haversine dan
        distribusi segitiga untuk waktu tempuh.
        """
        jarak_km = LayananRute.hitung_jarak_haversine(
            coord_asal[0], coord_asal[1], coord_tujuan[0], coord_tujuan[1]
        )
        waktu_tempuh_menit = np.random.triangular(
            left=WAKTU_TEMPUH_INTERNAL_MIN_MENIT,
            mode=WAKTU_TEMPUH_INTERNAL_MODE_MENIT,
            right=WAKTU_TEMPUH_INTERNAL_MAKS_MENIT,
        )
        waktu_tempuh_detik = waktu_tempuh_menit * 60

        return {
            "summary": {
                "lengthInMeters": jarak_km * 1000,
                "travelTimeInSeconds": waktu_tempuh_detik,
                "trafficDelayInSeconds": 0,
                "noTrafficTravelTimeInSeconds": waktu_tempuh_detik,
            },
            "legs": [
                {
                    "summary": {
                        "lengthInMeters": jarak_km * 1000,
                        "travelTimeInSeconds": waktu_tempuh_detik,
                    },
                    "points": [
                        {"latitude": coord_asal[0],  "longitude": coord_asal[1]},
                        {"latitude": coord_tujuan[0], "longitude": coord_tujuan[1]},
                    ],
                }
            ],
        }

    @staticmethod
    def dapatkan_rute_segmen(
        kota_asal: str,
        kota_tujuan: str,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
        fallback_ke_internal: bool = True,
    ) -> Optional[Dict]:
        """
        Mengambil data rute untuk satu segmen perjalanan.
        Otomatis fallback ke estimasi internal jika API gagal.
        """
        coord_asal = (KOTA_KOORDINAT[kota_asal][0], KOTA_KOORDINAT[kota_asal][1])
        coord_tujuan = (KOTA_KOORDINAT[kota_tujuan][0], KOTA_KOORDINAT[kota_tujuan][1])

        if mode_perutean == "Model Rute Internal (Non-API)":
            return LayananRute.estimasi_rute_internal(coord_asal, coord_tujuan)

        data_rute = LayananRute.ambil_data_rute_mapbox(
            coord_asal, coord_tujuan, hindari_lalu_lintas
        )
        if data_rute:
            return data_rute

        if fallback_ke_internal:
            print(
                f"  PERINGATAN: API Mapbox gagal untuk {kota_asal} → {kota_tujuan}. "
                f"Menggunakan fallback model rute internal."
            )
            return LayananRute.estimasi_rute_internal(coord_asal, coord_tujuan)

        return None


# =============================================================================
# BAGIAN 4 — KALKULATOR BIAYA
# =============================================================================

class KalkulatorBiaya:
    """Menyediakan kalkulasi biaya operasional untuk segmen perjalanan."""

    @staticmethod
    def hitung_biaya_segmen(
        jarak_km: float, waktu_tempuh_jam: float
    ) -> Tuple[float, float, float]:
        """
        Menghitung biaya BBM dan sopir untuk satu segmen perjalanan.

        Returns:
            Tuple (biaya_bbm, biaya_sopir, liter_bbm_terpakai)
        """
        konsumsi_bbm = random.uniform(
            MIN_KONSUMSI_BBM_LITER_PER_JAM, MAKS_KONSUMSI_BBM_LITER_PER_JAM
        )
        liter_bbm = konsumsi_bbm * waktu_tempuh_jam
        biaya_bbm = liter_bbm * TARIF_BBM
        biaya_sopir = waktu_tempuh_jam * GAJI_SOPIR_PER_JAM
        return biaya_bbm, biaya_sopir, liter_bbm

    @staticmethod
    def buat_ringkasan_trip(pengiriman: "Pengiriman", truk: "Truk") -> Dict:
        """Membuat dict ringkasan hasil satu trip pengiriman yang sudah selesai."""
        durasi_muat = pengiriman.estimasi_waktu_muat_menit
        durasi_bongkar = pengiriman.estimasi_waktu_bongkar_menit

        if pengiriman.waktu_penyelesaian_aktual > 0 and pengiriman.waktu_mulai_muat > 0:
            total_siklus_menit = (
                (pengiriman.waktu_penyelesaian_aktual - pengiriman.waktu_mulai_muat) / 60
            )
        else:
            total_siklus_menit = -1

        return {
            "id_pengiriman": pengiriman.id_pengiriman,
            "id_truk": truk.id_truk,
            "asal": pengiriman.kota_asal,
            "tujuan": pengiriman.kota_tujuan,
            "jarak_km": pengiriman.jarak_tempuh_km,
            "waktu_tempuh_aktual_menit": pengiriman.estimasi_waktu_tempuh_menit,
            "waktu_muat_menit": durasi_muat,
            "waktu_bongkar_menit": durasi_bongkar,
            "total_waktu_siklus_menit": total_siklus_menit,
            "status_akhir": pengiriman.status_pengiriman,
            "biaya_total": pengiriman.biaya_pengiriman_total,
            "waktu_permintaan_jam": pengiriman.waktu_permintaan_dibuat / 3600,
            "waktu_selesai_jam": (
                pengiriman.waktu_penyelesaian_aktual / 3600
                if pengiriman.waktu_penyelesaian_aktual > 0
                else -1
            ),
            "batas_sla_jam": pengiriman.batas_waktu_penyelesaian / 3600,
        }


# =============================================================================
# BAGIAN 5 — MESIN SIMULASI (Logika Inti & Skenario)
# =============================================================================

class MesinSimulasi:
    """
    Kelas inti simulasi. Menyimpan seluruh state (armada truk dan daftar
    pengiriman) sebagai atribut instance — bukan variabel global.

    Satu instance MesinSimulasi digunakan untuk satu run simulasi,
    sehingga beberapa simulasi dapat berjalan paralel tanpa konflik state.
    """

    def __init__(self):
        self.armada_truk: List[Truk] = []
        self.daftar_pengiriman: List[Pengiriman] = []

    # ─────────────────────────────────────────────────────────────
    # 5.1 INISIALISASI SISTEM
    # ─────────────────────────────────────────────────────────────

    def inisialisasi_armada(
        self,
        jumlah_truk: int,
        kapasitas_default_ton: float = 10.0,
        string_kota_depot: Optional[str] = None,
    ) -> None:
        """
        Membuat armada truk baru dan mereset semua penghitung ID.

        Args:
            jumlah_truk: Jumlah truk yang akan dibuat.
            kapasitas_default_ton: Kapasitas dasar truk (±variasi acak).
            string_kota_depot: String kota depot dipisah koma, mis. "Jakarta,Medan".
        """
        self.armada_truk = []
        Truk.penghitung_id = 0

        kota_depot_valid = self._parse_kota_depot(string_kota_depot)

        for _ in range(jumlah_truk):
            depot = random.choice(kota_depot_valid)
            kapasitas = kapasitas_default_ton + random.uniform(-2, 5)
            truk = Truk(kapasitas_ton=kapasitas, lokasi_depot=depot)
            self.armada_truk.append(truk)

        depot_digunakan = ", ".join(set(t.lokasi_depot for t in self.armada_truk))
        print(
            f"Inisialisasi {len(self.armada_truk)} truk. "
            f"Depot di: {depot_digunakan}"
        )

    def _parse_kota_depot(self, string_kota_depot: Optional[str]) -> List[str]:
        """Mengurai string kota depot dan mengembalikan daftar kota yang valid."""
        if string_kota_depot:
            nama_kota_masuk = [
                k.strip()
                for k in string_kota_depot.split(",")
                if k.strip()
            ]
            kota_valid = [k for k in nama_kota_masuk if k in KOTA_KOORDINAT]
            kota_tidak_valid = [k for k in nama_kota_masuk if k not in KOTA_KOORDINAT]

            for kota in kota_tidak_valid:
                print(f"Peringatan: Kota depot '{kota}' tidak ditemukan, diabaikan.")

            if kota_valid:
                return kota_valid

        return list(KOTA_KOORDINAT.keys())

    def buat_daftar_pengiriman(
        self,
        jumlah_permintaan: int,
        waktu_simulasi_awal: float = 0.0,
        durasi_generasi_hari: int = 1,
        mode_pengiriman: str = "Acak ke Acak",
        kota_asal_tetap: Optional[str] = None,
        kota_tujuan_tetap: Optional[str] = None,
    ) -> None:
        """
        Membuat daftar permintaan pengiriman secara stokastik sesuai mode yang dipilih.

        Args:
            jumlah_permintaan: Jumlah permintaan yang dibuat.
            waktu_simulasi_awal: Waktu awal simulasi dalam detik.
            durasi_generasi_hari: Rentang waktu pembuatan permintaan (hari).
            mode_pengiriman: Salah satu dari mode yang didukung.
            kota_asal_tetap: Kota asal tetap (jika mode memerlukannya).
            kota_tujuan_tetap: Kota tujuan tetap (jika mode memerlukannya).
        """
        self.daftar_pengiriman = []
        Pengiriman.penghitung_id = 0
        kota_tersedia = list(KOTA_KOORDINAT.keys())

        for _ in range(jumlah_permintaan):
            asal, tujuan = self._tentukan_asal_tujuan(
                mode_pengiriman, kota_tersedia, kota_asal_tetap, kota_tujuan_tetap
            )
            if asal is None or tujuan is None:
                continue

            waktu_dibuat = waktu_simulasi_awal + random.uniform(
                0, durasi_generasi_hari * 24 * 3600
            )
            pengiriman = Pengiriman(
                kota_asal=asal,
                kota_tujuan=tujuan,
                waktu_permintaan_dibuat=waktu_dibuat,
            )
            self.daftar_pengiriman.append(pengiriman)

        self.daftar_pengiriman.sort(key=lambda p: p.waktu_permintaan_dibuat)

    def _tentukan_asal_tujuan(
        self,
        mode: str,
        kota_tersedia: List[str],
        kota_asal_tetap: Optional[str],
        kota_tujuan_tetap: Optional[str],
    ) -> Tuple[Optional[str], Optional[str]]:
        """
        Menentukan pasangan asal-tujuan berdasarkan mode distribusi pengiriman.
        Mengembalikan (None, None) jika konfigurasi tidak valid.
        """
        if mode == "Satu Asal ke Satu Tujuan":
            if (
                kota_asal_tetap
                and kota_tujuan_tetap
                and kota_asal_tetap != kota_tujuan_tetap
            ):
                return kota_asal_tetap, kota_tujuan_tetap
            print("Peringatan: Mode 'Satu Asal ke Satu Tujuan' perlu asal & tujuan berbeda.")
            return None, None

        if mode == "Satu Asal ke Banyak Tujuan (Acak)":
            if not kota_asal_tetap:
                print("Peringatan: Mode ini memerlukan Kota Asal Tetap.")
                return None, None
            tujuan_alternatif = [k for k in kota_tersedia if k != kota_asal_tetap]
            if not tujuan_alternatif:
                print(f"Peringatan: Tidak ada tujuan alternatif untuk '{kota_asal_tetap}'.")
                return None, None
            return kota_asal_tetap, random.choice(tujuan_alternatif)

        if mode == "Banyak Asal (Acak) ke Satu Tujuan":
            if not kota_tujuan_tetap:
                print("Peringatan: Mode ini memerlukan Kota Tujuan Tetap.")
                return None, None
            asal_alternatif = [k for k in kota_tersedia if k != kota_tujuan_tetap]
            if not asal_alternatif:
                print(f"Peringatan: Tidak ada asal alternatif untuk '{kota_tujuan_tetap}'.")
                return None, None
            return random.choice(asal_alternatif), kota_tujuan_tetap

        # Default: "Acak ke Acak"
        if len(kota_tersedia) < 2:
            print("Peringatan: Mode 'Acak ke Acak' membutuhkan minimal 2 kota.")
            return None, None
        asal, tujuan = random.sample(kota_tersedia, 2)
        return asal, tujuan

    # ─────────────────────────────────────────────────────────────
    # 5.2 PEMROSESAN EVENT (Helper SRP)
    # ─────────────────────────────────────────────────────────────

    def _proses_muat_selesai(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_event: float,
    ) -> None:
        """Memperbarui state truk dan pengiriman saat proses muat barang selesai."""
        pengiriman.waktu_selesai_muat = waktu_event
        pengiriman.muat_selesai = True
        truk.muatan_saat_ini_ton += pengiriman.jumlah_barang_ton
        truk.total_jam_memuat += (pengiriman.estimasi_waktu_muat_menit / 60)

    def _proses_bongkar_selesai(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_event: float,
    ) -> None:
        """
        Memperbarui state truk dan pengiriman saat proses bongkar selesai.
        Menentukan status SLA (tepat waktu / terlambat) dan membebankan biaya pemeliharaan.
        """
        pengiriman.waktu_selesai_bongkar = waktu_event
        pengiriman.bongkar_selesai = True
        pengiriman.waktu_penyelesaian_aktual = waktu_event

        # Kurangi muatan truk
        truk.muatan_saat_ini_ton -= pengiriman.jumlah_barang_ton
        if truk.muatan_saat_ini_ton < 0.001:
            truk.muatan_saat_ini_ton = 0.0

        truk.total_jam_membongkar += (pengiriman.estimasi_waktu_bongkar_menit / 60)

        # Tentukan status SLA
        if waktu_event > pengiriman.batas_waktu_penyelesaian:
            pengiriman.status_pengiriman = "selesai_terlambat"
        else:
            pengiriman.status_pengiriman = "selesai"

        # Biaya pemeliharaan per trip
        pengiriman.biaya_pengiriman_total += BIAYA_PEMELIHARAAN_PER_TRIP
        truk.total_biaya_pemeliharaan += BIAYA_PEMELIHARAAN_PER_TRIP
        truk.jumlah_trip_selesai += 1

    def _catat_biaya_dan_metrik_mengemudi(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        jarak_km: float,
        waktu_tempuh_jam: float,
    ) -> None:
        """
        Menghitung biaya BBM & sopir, lalu mengakumulasikan ke objek truk dan pengiriman.
        (Dipecah dari simulate_actual_trip — mengikuti SRP)
        """
        biaya_bbm, biaya_sopir, _ = KalkulatorBiaya.hitung_biaya_segmen(
            jarak_km, waktu_tempuh_jam
        )
        pengiriman.biaya_pengiriman_total += biaya_bbm + biaya_sopir
        truk.total_biaya_bbm += biaya_bbm
        truk.total_biaya_sopir += biaya_sopir
        truk.total_km_operasional += jarak_km
        truk.total_jam_mengemudi += waktu_tempuh_jam

    def _perbarui_lokasi_truk(
        self, truk: Truk, nama_kota: str
    ) -> None:
        """Memperbarui lokasi dan koordinat truk ke kota yang dituju."""
        truk.lokasi_sekarang = nama_kota
        truk.koordinat_sekarang = (
            KOTA_KOORDINAT[nama_kota][0],
            KOTA_KOORDINAT[nama_kota][1],
        )

    def _simulasikan_perjalanan_aktual(
        self,
        pengiriman: Pengiriman,
        truk: Truk,
        ringkasan_rute: Dict,
        waktu_mulai_trip: float,
    ) -> Dict:
        """
        Mensimulasikan satu siklus penuh trip pengiriman secara sekuensial
        (digunakan oleh Simulasi Dasar).

        Tahapan: Muat → Berangkat → Tiba → Bongkar → Selesai.

        Returns:
            Dict ringkasan hasil trip (via KalkulatorBiaya.buat_ringkasan_trip).
        """
        # Tahap 1: Muat barang
        waktu_muat_detik = pengiriman.estimasi_waktu_muat_menit * 60
        pengiriman.waktu_mulai_muat = waktu_mulai_trip
        pengiriman.waktu_selesai_muat = waktu_mulai_trip + waktu_muat_detik
        truk.status = "memuat_barang"
        truk.total_jam_memuat += waktu_muat_detik / 3600

        # Tahap 2: Perjalanan ke tujuan
        pengiriman.waktu_keberangkatan = pengiriman.waktu_selesai_muat
        waktu_tempuh_detik = ringkasan_rute["travelTimeInSeconds"]
        jarak_km = ringkasan_rute["lengthInMeters"] / 1000

        pengiriman.estimasi_waktu_tempuh_menit = waktu_tempuh_detik / 60
        pengiriman.jarak_tempuh_km = jarak_km
        truk.status = "dalam_perjalanan_mengantar"
        truk.lokasi_sekarang = f"Menuju {pengiriman.kota_tujuan}"
        truk.destinasi_berikutnya = pengiriman.kota_tujuan

        self._catat_biaya_dan_metrik_mengemudi(
            truk, pengiriman, jarak_km, waktu_tempuh_detik / 3600
        )

        # Tahap 3: Tiba dan bongkar barang
        pengiriman.waktu_tiba_tujuan = (
            pengiriman.waktu_keberangkatan + waktu_tempuh_detik
        )
        pengiriman.waktu_mulai_bongkar = pengiriman.waktu_tiba_tujuan
        waktu_bongkar_detik = pengiriman.estimasi_waktu_bongkar_menit * 60
        pengiriman.waktu_selesai_bongkar = (
            pengiriman.waktu_mulai_bongkar + waktu_bongkar_detik
        )
        truk.status = "membongkar_barang"
        truk.total_jam_membongkar += waktu_bongkar_detik / 3600

        # Tahap 4: Finalisasi status
        pengiriman.waktu_penyelesaian_aktual = pengiriman.waktu_selesai_bongkar
        if pengiriman.waktu_penyelesaian_aktual > pengiriman.batas_waktu_penyelesaian:
            pengiriman.status_pengiriman = "selesai_terlambat"
        else:
            pengiriman.status_pengiriman = "selesai"

        truk.muatan_saat_ini_ton = 0.0
        truk.id_pengiriman_aktif = None
        self._perbarui_lokasi_truk(truk, pengiriman.kota_tujuan)
        truk.waktu_event_berikutnya = pengiriman.waktu_penyelesaian_aktual
        truk.jumlah_trip_selesai += 1
        truk.total_biaya_pemeliharaan += BIAYA_PEMELIHARAAN_PER_TRIP
        pengiriman.biaya_pengiriman_total += BIAYA_PEMELIHARAAN_PER_TRIP

        return KalkulatorBiaya.buat_ringkasan_trip(pengiriman, truk)

    # ─────────────────────────────────────────────────────────────
    # 5.3 SKENARIO: SIMULASI DASAR
    # ─────────────────────────────────────────────────────────────

    def jalankan_simulasi_dasar(
        self,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
        nomor_run: int,
    ) -> Tuple[List[Dict], List[Pengiriman]]:
        """
        Simulasi paling sederhana: truk tersedia pertama kali langsung
        mengambil permintaan pengiriman secara sekuensial (FCFS).
        """
        waktu_simulasi = 0.0
        antrian_pengiriman = sorted(
            [p for p in self.daftar_pengiriman if p.status_pengiriman == "menunggu_alokasi_truk"],
            key=lambda p: p.waktu_permintaan_dibuat,
        )
        pengiriman_diproses: List[Pengiriman] = list(self.daftar_pengiriman)
        hasil_trip: List[Dict] = []

        self._reset_status_armada()
        id_diproses = set()

        for pengiriman_ref in antrian_pengiriman:
            pengiriman = next(
                (p for p in pengiriman_diproses if p.id_pengiriman == pengiriman_ref.id_pengiriman),
                None,
            )
            kondisi_skip = (
                pengiriman is None
                or pengiriman.id_pengiriman in id_diproses
                or pengiriman.status_pengiriman != "menunggu_alokasi_truk"
            )
            if kondisi_skip:
                continue

            if pengiriman.waktu_permintaan_dibuat > waktu_simulasi:
                waktu_simulasi = pengiriman.waktu_permintaan_dibuat

            self.armada_truk.sort(key=lambda t: t.waktu_event_berikutnya)
            truk_terpilih = self._pilih_truk_tersedia(
                waktu_simulasi, pengiriman.jumlah_barang_ton
            )

            if truk_terpilih is None:
                if pengiriman.status_pengiriman == "menunggu_alokasi_truk":
                    pengiriman.status_pengiriman = "tidak_ada_truk_tersedia"
                continue

            id_diproses.add(pengiriman.id_pengiriman)
            waktu_mulai = max(waktu_simulasi, truk_terpilih.waktu_event_berikutnya)

            # Perjalanan depot ke lokasi muat (jika berbeda kota)
            if truk_terpilih.lokasi_sekarang != pengiriman.kota_asal:
                berhasil = self._proses_perjalanan_ke_lokasi_muat(
                    truk_terpilih, pengiriman, waktu_mulai, mode_perutean, hindari_lalu_lintas
                )
                if not berhasil:
                    truk_terpilih.waktu_event_berikutnya = waktu_mulai
                    continue
                waktu_mulai = truk_terpilih.waktu_event_berikutnya

            # Alokasi truk ke pengiriman
            pengiriman.id_truk_ditugaskan = truk_terpilih.id_truk
            pengiriman.status_pengiriman = "dialokasikan_ke_truk"
            pengiriman.waktu_truk_dialokasikan = waktu_mulai
            truk_terpilih.status = "menunggu_muat"
            truk_terpilih.id_pengiriman_aktif = pengiriman.id_pengiriman

            # Pengambilan rute utama dan simulasi trip
            rute_utama = LayananRute.dapatkan_rute_segmen(
                pengiriman.kota_asal, pengiriman.kota_tujuan,
                mode_perutean, hindari_lalu_lintas,
            )
            if rute_utama and "summary" in rute_utama:
                pengiriman.rute_utama_json = rute_utama
                data_trip = self._simulasikan_perjalanan_aktual(
                    pengiriman, truk_terpilih,
                    rute_utama["summary"], pengiriman.waktu_truk_dialokasikan,
                )
                hasil_trip.append(data_trip)
                waktu_simulasi = max(waktu_simulasi, truk_terpilih.waktu_event_berikutnya)
            else:
                pengiriman.status_pengiriman = "gagal_rute_utama"
                truk_terpilih.status = "siaga_di_depot"
                truk_terpilih.waktu_event_berikutnya = pengiriman.waktu_truk_dialokasikan

        # Tandai pengiriman yang tidak sempat diproses
        for p in pengiriman_diproses:
            if (
                p.id_pengiriman not in id_diproses
                and p.status_pengiriman == "menunggu_alokasi_truk"
            ):
                p.status_pengiriman = "tidak_terproses_final_dasar"

        return hasil_trip, pengiriman_diproses

    # ─────────────────────────────────────────────────────────────
    # 5.4 SKENARIO 1: RUTE TETAP & PENJADWALAN STATIS
    # ─────────────────────────────────────────────────────────────

    def jalankan_skenario1(
        self,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
        nomor_run: int,
    ) -> Tuple[List[Dict], List[Pengiriman]]:
        """
        Skenario 1: Penjadwalan statis — setiap truk mendapat satu pengiriman
        di awal, kemudian event loop memproses trip secara berurutan.
        Tidak ada lalu lintas real-time (hindari_lalu_lintas=False by default).
        """
        pengiriman_diproses: List[Pengiriman] = list(self.daftar_pengiriman)
        hasil_trip: List[Dict] = []
        jadwal_per_truk: Dict[str, List[Pengiriman]] = defaultdict(list)

        antrian = sorted(
            [p for p in pengiriman_diproses if p.status_pengiriman == "menunggu_alokasi_truk"],
            key=lambda p: p.waktu_permintaan_dibuat,
        )

        # Fase penjadwalan statis: distribusi satu pengiriman per truk
        salinan_armada = list(self.armada_truk)
        for p_obj in antrian:
            salinan_armada.sort(key=lambda t: len(jadwal_per_truk.get(t.id_truk, [])))
            for truk in salinan_armada:
                if (
                    not jadwal_per_truk[truk.id_truk]
                    and truk.bisa_angkut(p_obj.jumlah_barang_ton)
                ):
                    jadwal_per_truk[truk.id_truk].append(p_obj)
                    p_obj.id_truk_ditugaskan = truk.id_truk
                    p_obj.status_pengiriman = "dijadwalkan_statis_s1"
                    break
            else:
                p_obj.status_pengiriman = "tidak_terjadwal_statis_s1"

        # Reset & isi jadwal tiap truk
        for truk in self.armada_truk:
            truk.jadwal_tugas_statis = jadwal_per_truk.get(truk.id_truk, [])
            truk.indeks_tugas_statis = 0
            truk.waktu_event_berikutnya = 0
            self._perbarui_lokasi_truk(truk, truk.lokasi_depot)
            truk.status = "siaga_di_depot"
            truk.muatan_saat_ini_ton = 0.0

        # Buat antrian event awal
        antrian_event: List[Tuple[float, str, str]] = []
        for truk in self.armada_truk:
            if truk.jadwal_tugas_statis:
                antrian_event.append((0.0, "CEK_TUGAS_STATIS_S1", truk.id_truk))
        antrian_event.sort()

        waktu_simulasi = 0.0
        id_event_diproses = set()

        while antrian_event:
            waktu_event, tipe_event, id_entitas = antrian_event.pop(0)
            waktu_simulasi = max(waktu_simulasi, waktu_event)

            truk_event, pengiriman_event = self._resolve_entitas(
                id_entitas, pengiriman_diproses
            )
            if truk_event is None and pengiriman_event is None:
                continue

            if tipe_event == "CEK_TUGAS_STATIS_S1" and truk_event:
                self._handle_cek_tugas_s1(
                    truk_event, pengiriman_diproses, id_event_diproses,
                    waktu_simulasi, antrian_event, mode_perutean, hindari_lalu_lintas,
                )

            elif tipe_event == "MULAI_MUAT_S1" and pengiriman_event and truk_event:
                self._handle_mulai_muat_s1(
                    truk_event, pengiriman_event, waktu_simulasi, antrian_event
                )

            elif tipe_event == "SELESAI_MUAT_S1" and pengiriman_event and truk_event:
                self._handle_selesai_muat_s1(
                    truk_event, pengiriman_event, waktu_simulasi,
                    antrian_event, mode_perutean, hindari_lalu_lintas,
                )

            elif tipe_event == "TIBA_TUJUAN_S1" and pengiriman_event and truk_event:
                self._handle_tiba_tujuan_s1(
                    truk_event, pengiriman_event, waktu_simulasi, antrian_event
                )

            elif tipe_event == "MULAI_BONGKAR_S1" and pengiriman_event and truk_event:
                self._handle_mulai_bongkar_s1(
                    truk_event, pengiriman_event, waktu_simulasi, antrian_event
                )

            elif tipe_event == "SELESAI_BONGKAR_S1" and pengiriman_event and truk_event:
                self._handle_selesai_bongkar_s1(
                    truk_event, pengiriman_event, waktu_simulasi,
                    antrian_event, hasil_trip,
                )

            antrian_event.sort()

        return hasil_trip, pengiriman_diproses

    def _handle_cek_tugas_s1(
        self,
        truk: Truk,
        pengiriman_diproses: List[Pengiriman],
        id_event_diproses: set,
        waktu_simulasi: float,
        antrian_event: List,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
    ) -> None:
        """Handler event CEK_TUGAS_STATIS_S1."""
        status_valid = truk.status in ["siaga_di_depot", "siaga_setelah_bongkar"]
        if not status_valid:
            return
        if truk.indeks_tugas_statis >= len(truk.jadwal_tugas_statis):
            return

        p_obj = truk.jadwal_tugas_statis[truk.indeks_tugas_statis]
        if p_obj.id_pengiriman in id_event_diproses:
            return

        waktu_mulai = max(waktu_simulasi, p_obj.waktu_permintaan_dibuat)
        id_event_diproses.add(p_obj.id_pengiriman)
        waktu_event_berikutnya = waktu_mulai

        # Perjalanan ke lokasi muat (jika diperlukan)
        if truk.lokasi_sekarang != p_obj.kota_asal:
            rute_muat = LayananRute.dapatkan_rute_segmen(
                truk.lokasi_sekarang, p_obj.kota_asal, mode_perutean, hindari_lalu_lintas
            )
            if rute_muat and "summary" in rute_muat:
                p_obj.rute_depot_ke_asal_json = rute_muat
                ringkasan = rute_muat["summary"]
                durasi_detik = ringkasan["travelTimeInSeconds"]
                jarak_km = ringkasan["lengthInMeters"] / 1000
                self._catat_biaya_dan_metrik_mengemudi(
                    truk, p_obj, jarak_km, durasi_detik / 3600
                )
                waktu_event_berikutnya += durasi_detik
                self._perbarui_lokasi_truk(truk, p_obj.kota_asal)
            else:
                p_obj.status_pengiriman = f"gagal_rute_muat_s1_{p_obj.id_pengiriman}"
                truk.indeks_tugas_statis += 1
                antrian_event.append(
                    (waktu_event_berikutnya, "CEK_TUGAS_STATIS_S1", truk.id_truk)
                )
                return

        p_obj.waktu_truk_dialokasikan = waktu_event_berikutnya
        truk.status = "menunggu_muat_s1"
        truk.id_pengiriman_aktif = p_obj.id_pengiriman
        antrian_event.append(
            (waktu_event_berikutnya, "MULAI_MUAT_S1", p_obj.id_pengiriman)
        )

    def _handle_mulai_muat_s1(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_simulasi: float,
        antrian_event: List,
    ) -> None:
        """Handler event MULAI_MUAT_S1."""
        truk.status = "memuat_barang"
        pengiriman.waktu_mulai_muat = waktu_simulasi
        durasi_muat_detik = pengiriman.estimasi_waktu_muat_menit * 60
        pengiriman.waktu_selesai_muat = waktu_simulasi + durasi_muat_detik
        truk.total_jam_memuat += durasi_muat_detik / 3600
        antrian_event.append(
            (pengiriman.waktu_selesai_muat, "SELESAI_MUAT_S1", pengiriman.id_pengiriman)
        )

    def _handle_selesai_muat_s1(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_simulasi: float,
        antrian_event: List,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
    ) -> None:
        """Handler event SELESAI_MUAT_S1."""
        truk.muatan_saat_ini_ton = pengiriman.jumlah_barang_ton
        pengiriman.waktu_keberangkatan = waktu_simulasi

        rute_utama = LayananRute.dapatkan_rute_segmen(
            pengiriman.kota_asal, pengiriman.kota_tujuan, mode_perutean, hindari_lalu_lintas
        )
        if rute_utama and "summary" in rute_utama:
            pengiriman.rute_utama_json = rute_utama
            ringkasan = rute_utama["summary"]
            durasi_detik = ringkasan["travelTimeInSeconds"]
            jarak_km = ringkasan["lengthInMeters"] / 1000
            self._catat_biaya_dan_metrik_mengemudi(
                truk, pengiriman, jarak_km, durasi_detik / 3600
            )
            pengiriman.jarak_tempuh_km = jarak_km
            pengiriman.estimasi_waktu_tempuh_menit = durasi_detik / 60
            truk.status = "dalam_perjalanan_mengantar"
            antrian_event.append(
                (waktu_simulasi + durasi_detik, "TIBA_TUJUAN_S1", pengiriman.id_pengiriman)
            )
        else:
            pengiriman.status_pengiriman = "gagal_rute_utama_s1"
            truk.status = "siaga_di_depot"
            truk.indeks_tugas_statis += 1
            antrian_event.append(
                (waktu_simulasi, "CEK_TUGAS_STATIS_S1", truk.id_truk)
            )

    def _handle_tiba_tujuan_s1(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_simulasi: float,
        antrian_event: List,
    ) -> None:
        """Handler event TIBA_TUJUAN_S1."""
        self._perbarui_lokasi_truk(truk, pengiriman.kota_tujuan)
        pengiriman.waktu_tiba_tujuan = waktu_simulasi
        truk.status = "menunggu_bongkar_s1"
        antrian_event.append(
            (waktu_simulasi, "MULAI_BONGKAR_S1", pengiriman.id_pengiriman)
        )

    def _handle_mulai_bongkar_s1(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_simulasi: float,
        antrian_event: List,
    ) -> None:
        """Handler event MULAI_BONGKAR_S1."""
        truk.status = "membongkar_barang"
        pengiriman.waktu_mulai_bongkar = waktu_simulasi
        durasi_bongkar_detik = pengiriman.estimasi_waktu_bongkar_menit * 60
        pengiriman.waktu_selesai_bongkar = waktu_simulasi + durasi_bongkar_detik
        truk.total_jam_membongkar += durasi_bongkar_detik / 60
        antrian_event.append(
            (pengiriman.waktu_selesai_bongkar, "SELESAI_BONGKAR_S1", pengiriman.id_pengiriman)
        )

    def _handle_selesai_bongkar_s1(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_simulasi: float,
        antrian_event: List,
        hasil_trip: List[Dict],
    ) -> None:
        """Handler event SELESAI_BONGKAR_S1."""
        self._proses_bongkar_selesai(truk, pengiriman, waktu_simulasi)
        hasil_trip.append(KalkulatorBiaya.buat_ringkasan_trip(pengiriman, truk))
        truk.indeks_tugas_statis += 1
        truk.waktu_event_berikutnya = waktu_simulasi
        truk.status = "siaga_setelah_bongkar"
        antrian_event.append(
            (waktu_simulasi, "CEK_TUGAS_STATIS_S1", truk.id_truk)
        )

    # ─────────────────────────────────────────────────────────────
    # 5.5 SKENARIO 2: RUTE DINAMIS & ALOKASI INTER-TRUK
    # ─────────────────────────────────────────────────────────────

    def jalankan_skenario2(
        self,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
        nomor_run: int,
    ) -> Tuple[List[Dict], List[Pengiriman]]:
        """
        Skenario 2: Alokasi dinamis — truk dilepas ke pasar permintaan,
        truk siaga yang paling dekat dengan lokasi muat diprioritaskan.
        Mendukung lalu lintas real-time.
        """
        pengiriman_diproses: List[Pengiriman] = list(self.daftar_pengiriman)
        hasil_trip: List[Dict] = []
        self._reset_status_armada()

        antrian_event: List[Tuple[float, str, str]] = []
        for p in pengiriman_diproses:
            if p.status_pengiriman == "menunggu_alokasi_truk":
                antrian_event.append(
                    (p.waktu_permintaan_dibuat, "PERMINTAAN_BARU_S2", p.id_pengiriman)
                )
        for t in self.armada_truk:
            antrian_event.append((0.0, "TRUK_SIAGA_CEK_TUGAS_S2", t.id_truk))

        antrian_event.sort()
        waktu_simulasi = 0.0
        id_pengiriman_diproses = set()

        while antrian_event:
            waktu_event, tipe_event, data_id = antrian_event.pop(0)
            waktu_simulasi = max(waktu_simulasi, waktu_event)

            truk_event, pengiriman_event = self._resolve_entitas(
                data_id, pengiriman_diproses
            )
            if truk_event is None and pengiriman_event is None:
                continue

            if tipe_event == "PERMINTAAN_BARU_S2":
                for t_siaga in self.armada_truk:
                    if t_siaga.apakah_siaga(waktu_simulasi):
                        sudah_ada = any(
                            ev[1] == "TRUK_SIAGA_CEK_TUGAS_S2"
                            and ev[2] == t_siaga.id_truk
                            and ev[0] <= waktu_simulasi + 1
                            for ev in antrian_event
                        )
                        if not sudah_ada:
                            antrian_event.append(
                                (waktu_simulasi, "TRUK_SIAGA_CEK_TUGAS_S2", t_siaga.id_truk)
                            )

            elif tipe_event == "TRUK_SIAGA_CEK_TUGAS_S2" and truk_event:
                self._handle_cek_tugas_s2(
                    truk_event, pengiriman_diproses, id_pengiriman_diproses,
                    waktu_simulasi, antrian_event, mode_perutean, hindari_lalu_lintas,
                )

            elif tipe_event == "MULAI_MUAT_S2" and pengiriman_event and truk_event:
                truk_event.status = "memuat_barang"
                pengiriman_event.waktu_mulai_muat = waktu_simulasi
                durasi_muat_detik = pengiriman_event.estimasi_waktu_muat_menit * 60
                pengiriman_event.waktu_selesai_muat = waktu_simulasi + durasi_muat_detik
                truk_event.total_jam_memuat += durasi_muat_detik / 3600
                antrian_event.append(
                    (pengiriman_event.waktu_selesai_muat, "SELESAI_MUAT_S2", pengiriman_event.id_pengiriman)
                )

            elif tipe_event == "SELESAI_MUAT_S2" and pengiriman_event and truk_event:
                truk_event.muatan_saat_ini_ton = pengiriman_event.jumlah_barang_ton
                pengiriman_event.waktu_keberangkatan = waktu_simulasi

                rute_utama = LayananRute.dapatkan_rute_segmen(
                    pengiriman_event.kota_asal, pengiriman_event.kota_tujuan,
                    mode_perutean, hindari_lalu_lintas,
                )
                if rute_utama and "summary" in rute_utama:
                    pengiriman_event.rute_utama_json = rute_utama
                    ringkasan = rute_utama["summary"]
                    durasi_detik = ringkasan["travelTimeInSeconds"]
                    jarak_km = ringkasan["lengthInMeters"] / 1000
                    self._catat_biaya_dan_metrik_mengemudi(
                        truk_event, pengiriman_event, jarak_km, durasi_detik / 3600
                    )
                    pengiriman_event.jarak_tempuh_km = jarak_km
                    pengiriman_event.estimasi_waktu_tempuh_menit = durasi_detik / 60
                    truk_event.status = "dalam_perjalanan_mengantar"
                    antrian_event.append(
                        (waktu_simulasi + durasi_detik, "TIBA_TUJUAN_S2", pengiriman_event.id_pengiriman)
                    )
                else:
                    pengiriman_event.status_pengiriman = "gagal_rute_utama_s2"
                    truk_event.status = "siaga_di_depot"
                    antrian_event.append(
                        (waktu_simulasi, "TRUK_SIAGA_CEK_TUGAS_S2", truk_event.id_truk)
                    )

            elif tipe_event == "TIBA_TUJUAN_S2" and pengiriman_event and truk_event:
                self._perbarui_lokasi_truk(truk_event, pengiriman_event.kota_tujuan)
                pengiriman_event.waktu_tiba_tujuan = waktu_simulasi
                truk_event.status = "menunggu_bongkar_s2"
                antrian_event.append(
                    (waktu_simulasi, "MULAI_BONGKAR_S2", pengiriman_event.id_pengiriman)
                )

            elif tipe_event == "MULAI_BONGKAR_S2" and pengiriman_event and truk_event:
                truk_event.status = "membongkar_barang"
                pengiriman_event.waktu_mulai_bongkar = waktu_simulasi
                durasi_bongkar_detik = pengiriman_event.estimasi_waktu_bongkar_menit * 60
                pengiriman_event.waktu_selesai_bongkar = waktu_simulasi + durasi_bongkar_detik
                truk_event.total_jam_membongkar += durasi_bongkar_detik / 60
                antrian_event.append(
                    (pengiriman_event.waktu_selesai_bongkar, "SELESAI_BONGKAR_S2", pengiriman_event.id_pengiriman)
                )

            elif tipe_event == "SELESAI_BONGKAR_S2" and pengiriman_event and truk_event:
                self._proses_bongkar_selesai(truk_event, pengiriman_event, waktu_simulasi)
                hasil_trip.append(KalkulatorBiaya.buat_ringkasan_trip(pengiriman_event, truk_event))
                truk_event.waktu_event_berikutnya = waktu_simulasi
                truk_event.status = "siaga_setelah_bongkar"
                truk_event.id_pengiriman_aktif = None
                antrian_event.append(
                    (waktu_simulasi, "TRUK_SIAGA_CEK_TUGAS_S2", truk_event.id_truk)
                )

            antrian_event.sort()

        # Tandai pengiriman yang tidak sempat teralokasi
        for p in pengiriman_diproses:
            if (
                p.id_pengiriman not in id_pengiriman_diproses
                and p.status_pengiriman == "menunggu_alokasi_truk"
            ):
                p.status_pengiriman = "tidak_terproses_s2_final"

        return hasil_trip, pengiriman_diproses

    def _handle_cek_tugas_s2(
        self,
        truk: Truk,
        pengiriman_diproses: List[Pengiriman],
        id_pengiriman_diproses: set,
        waktu_simulasi: float,
        antrian_event: List,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
    ) -> None:
        """Handler TRUK_SIAGA_CEK_TUGAS_S2 — memilih pengiriman terdekat untuk truk."""
        if not truk.apakah_siaga(waktu_simulasi):
            return

        kandidat = sorted(
            [
                p for p in pengiriman_diproses
                if (
                    p.status_pengiriman == "menunggu_alokasi_truk"
                    and p.waktu_permintaan_dibuat <= waktu_simulasi
                    and p.id_pengiriman not in id_pengiriman_diproses
                )
            ],
            key=lambda p: p.batas_waktu_penyelesaian,
        )

        pengiriman_terpilih: Optional[Pengiriman] = None
        waktu_tempuh_minimum = float("inf")
        # Skor optimal: gabungan antara efisiensi jarak (waktu_ke_muat) dan biaya (tarif)
        skor_optimal = float("inf")

        for p_cek in kandidat:
            if not truk.bisa_angkut(p_cek.jumlah_barang_ton):
                continue
            
            waktu_ke_muat = 0.0
            if truk.lokasi_sekarang != p_cek.kota_asal:
                rute_ke_muat = LayananRute.dapatkan_rute_segmen(
                    truk.lokasi_sekarang, p_cek.kota_asal, mode_perutean, hindari_lalu_lintas
                )
                if rute_ke_muat and "summary" in rute_ke_muat:
                    waktu_ke_muat = rute_ke_muat["summary"]["travelTimeInSeconds"]
                else:
                    waktu_ke_muat = float("inf")
            
            # LOGIKANOTE 1: Memilih yang paling murah per KM (tarif)
            # LOGIKANOTE 2: Memilih yang lokasinya paling dekat (backhauling)
            # Semakin kecil skor, semakin layak truk tersebut mengambil paket ini.
            skor_saat_ini = (waktu_ke_muat * 0.4) + (truk.tarif_per_km * 0.6)
            
            if skor_saat_ini < skor_optimal:
                skor_optimal = skor_saat_ini
                waktu_tempuh_minimum = waktu_ke_muat
                pengiriman_terpilih = p_cek
                
        # 1. Validasi Dulu: Pastikan ada paket yang terpilih
        if pengiriman_terpilih is None:
            return

        # 2. Simpan Data Optimasi ke Objek Pengiriman 
        is_backhaul = (waktu_tempuh_minimum == 0)
        pengiriman_terpilih.info_is_backhaul = is_backhaul
        pengiriman_terpilih.info_jenis_truk = truk.jenis_truk
        pengiriman_terpilih.info_tarif_truk = truk.tarif_per_km

        # 3. Lanjutkan Proses Alokasi
        id_pengiriman_diproses.add(pengiriman_terpilih.id_pengiriman)
        pengiriman_terpilih.id_truk_ditugaskan = truk.id_truk
        pengiriman_terpilih.status_pengiriman = "dialokasikan_ke_truk"
        waktu_event_berikutnya = waktu_simulasi

        if truk.lokasi_sekarang != pengiriman_terpilih.kota_asal:
            rute_ke_muatan = LayananRute.dapatkan_rute_segmen(
                truk.lokasi_sekarang, pengiriman_terpilih.kota_asal,
                mode_perutean, hindari_lalu_lintas,
            )
            if rute_ke_muatan and "summary" in rute_ke_muatan:
                pengiriman_terpilih.rute_depot_ke_asal_json = rute_ke_muatan
                ringkasan = rute_ke_muatan["summary"]
                durasi_detik = ringkasan["travelTimeInSeconds"]
                jarak_km = ringkasan["lengthInMeters"] / 1000
                self._catat_biaya_dan_metrik_mengemudi(
                    truk, pengiriman_terpilih, jarak_km, durasi_detik / 3600
                )
                waktu_event_berikutnya += durasi_detik
                self._perbarui_lokasi_truk(truk, pengiriman_terpilih.kota_asal)
            else:
                pengiriman_terpilih.status_pengiriman = "gagal_rute_ke_muatan_s2"
                antrian_event.append(
                    (waktu_event_berikutnya, "TRUK_SIAGA_CEK_TUGAS_S2", truk.id_truk)
                )
                return

        pengiriman_terpilih.waktu_truk_dialokasikan = waktu_event_berikutnya
        truk.status = "menunggu_muat_s2"
        truk.id_pengiriman_aktif = pengiriman_terpilih.id_pengiriman
        antrian_event.append(
            (waktu_event_berikutnya, "MULAI_MUAT_S2", pengiriman_terpilih.id_pengiriman)
        )

    # ─────────────────────────────────────────────────────────────
    # 5.6 SKENARIO 3: KONSOLIDASI PENGIRIMAN (TUR GABUNGAN)
    # ─────────────────────────────────────────────────────────────

    def jalankan_skenario3(
        self,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
        nomor_run: int,
    ) -> Tuple[List[Dict], List[Pengiriman]]:
        """
        Skenario 3: Konsolidasi — truk mengambil beberapa pengiriman dari kota asal
        yang sama dalam satu tur, kemudian mengantarkan satu per satu ke tujuan masing-masing.
        """
        pengiriman_diproses: List[Pengiriman] = list(self.daftar_pengiriman)
        hasil_trip: List[Dict] = []
        waktu_simulasi_global = 0.0

        for truk in self.armada_truk:
            self._reset_truk_untuk_skenario3(truk)

        # Fase pembentukan tur
        lanjutkan_pembentukan_tur = True
        while lanjutkan_pembentukan_tur:
            lanjutkan_pembentukan_tur = False
            sisa_pengiriman = sorted(
                [p for p in pengiriman_diproses if p.status_pengiriman == "menunggu_alokasi_truk"],
                key=lambda p: p.waktu_permintaan_dibuat,
            )
            if not sisa_pengiriman:
                break

            for truk in self.armada_truk:
                if truk.apakah_siaga(waktu_simulasi_global) and not truk.tur_konsolidasi:
                    tur_baru = self._bentuk_tur_konsolidasi(sisa_pengiriman, truk)
                    if tur_baru:
                        truk.tur_konsolidasi = tur_baru
                        truk.status = "ditugaskan_tur_s3"
                        truk.indeks_waypoint_tur = 0
                        lanjutkan_pembentukan_tur = True
                        for p_tur, _ in tur_baru:
                            p_tur.id_truk_ditugaskan = truk.id_truk

        # Buat antrian event dari tur yang sudah terbentuk
        antrian_event: List[Tuple[float, str, str]] = []
        for truk in self.armada_truk:
            if truk.tur_konsolidasi and truk.status == "ditugaskan_tur_s3":
                waktu_mulai_tur = truk.waktu_event_berikutnya
                for p_tur, _ in truk.tur_konsolidasi:
                    waktu_mulai_tur = max(waktu_mulai_tur, p_tur.waktu_permintaan_dibuat)
                antrian_event.append((waktu_mulai_tur, "LANJUT_TUR_S3", truk.id_truk))
        antrian_event.sort()

        id_waypoint_diproses = set()

        while antrian_event:
            waktu_event, tipe_event, id_truk_event = antrian_event.pop(0)
            waktu_simulasi_global = max(waktu_simulasi_global, waktu_event)

            truk_event = next(
                (t for t in self.armada_truk if t.id_truk == id_truk_event), None
            )
            if truk_event is None or truk_event.status == "siaga_setelah_tur":
                continue

            if tipe_event == "LANJUT_TUR_S3":
                self._handle_lanjut_tur_s3(
                    truk_event, id_waypoint_diproses, waktu_simulasi_global,
                    antrian_event, hasil_trip, mode_perutean, hindari_lalu_lintas,
                )
            antrian_event.sort()

        # Tandai pengiriman yang tidak sempat terproses
        for p_sisa in pengiriman_diproses:
            status_belum_selesai = p_sisa.status_pengiriman in [
                "menunggu_alokasi_truk",
                "dijadwalkan_konsolidasi_s3",
            ]
            if status_belum_selesai and not p_sisa.bongkar_selesai:
                p_sisa.status_pengiriman = "tidak_terproses_s3_final"

        return hasil_trip, pengiriman_diproses

    def _bentuk_tur_konsolidasi(
        self,
        daftar_pengiriman_tersisa: List[Pengiriman],
        truk: Truk,
        maks_pengiriman_per_tur: int = 2,
    ) -> Optional[List[Tuple[Pengiriman, str]]]:
        """
        Membentuk tur konsolidasi: mengumpulkan beberapa pengiriman dari
        kota asal yang sama, lalu menyusun urutan pickup → delivery.
        """
        if not truk.apakah_siaga(0):
            return None

        tersedia = sorted(
            [p for p in daftar_pengiriman_tersisa if p.status_pengiriman == "menunggu_alokasi_truk"],
            key=lambda p: p.waktu_permintaan_dibuat,
        )

        # Pilih pengiriman utama (yang pertama bisa diangkut)
        p_utama: Optional[Pengiriman] = None
        for p in tersedia:
            if truk.bisa_angkut(p.jumlah_barang_ton):
                p_utama = p
                break
        if p_utama is None:
            return None

        pengiriman_dalam_tur = [p_utama]
        muatan_tur = p_utama.jumlah_barang_ton
        p_utama.status_pengiriman = "dijadwalkan_konsolidasi_s3"

        # Coba tambah pengiriman lain dari kota asal yang sama
        if maks_pengiriman_per_tur > 1:
            for p_tambahan in tersedia:
                if len(pengiriman_dalam_tur) >= maks_pengiriman_per_tur:
                    break
                kondisi_tambah = (
                    p_tambahan.id_pengiriman != p_utama.id_pengiriman
                    and p_tambahan.status_pengiriman == "menunggu_alokasi_truk"
                    and p_tambahan.kota_asal == p_utama.kota_asal
                    and truk.bisa_angkut(muatan_tur + p_tambahan.jumlah_barang_ton)
                )
                if kondisi_tambah:
                    pengiriman_dalam_tur.append(p_tambahan)
                    muatan_tur += p_tambahan.jumlah_barang_ton
                    p_tambahan.status_pengiriman = "dijadwalkan_konsolidasi_s3"

        if not pengiriman_dalam_tur:
            return None

        # Susun waypoints: semua pickup terlebih dahulu, lalu delivery
        kota_asal_tur = pengiriman_dalam_tur[0].kota_asal
        tur: List[Tuple[Pengiriman, str]] = []

        for urutan, p_tur in enumerate(pengiriman_dalam_tur):
            tur.append((p_tur, "pickup"))
            p_tur.urutan_dalam_tur = urutan + 1

        pengiriman_untuk_delivery = sorted(
            pengiriman_dalam_tur,
            key=lambda p: LayananRute.hitung_jarak_haversine(
                KOTA_KOORDINAT[kota_asal_tur][0], KOTA_KOORDINAT[kota_asal_tur][1],
                KOTA_KOORDINAT[p.kota_tujuan][0], KOTA_KOORDINAT[p.kota_tujuan][1],
            ) if p.kota_tujuan in KOTA_KOORDINAT and kota_asal_tur in KOTA_KOORDINAT
            else float("inf"),
        )
        for urutan_d, p_deliv in enumerate(pengiriman_untuk_delivery):
            tur.append((p_deliv, "delivery"))
            p_deliv.urutan_dalam_tur = len(pengiriman_dalam_tur) + urutan_d + 1

        return tur

    def _handle_lanjut_tur_s3(
        self,
        truk: Truk,
        id_waypoint_diproses: set,
        waktu_simulasi: float,
        antrian_event: List,
        hasil_trip: List[Dict],
        mode_perutean: str,
        hindari_lalu_lintas: bool,
    ) -> None:
        """Handler LANJUT_TUR_S3 — memproses satu waypoint dalam tur konsolidasi."""
        if (
            not truk.tur_konsolidasi
            or truk.indeks_waypoint_tur >= len(truk.tur_konsolidasi)
        ):
            truk.status = "siaga_setelah_tur"
            return

        waktu_aktif = waktu_simulasi
        pengiriman_wp, tipe_wp = truk.tur_konsolidasi[truk.indeks_waypoint_tur]
        kunci_waypoint = (
            truk.id_truk,
            pengiriman_wp.id_pengiriman,
            tipe_wp,
            truk.indeks_waypoint_tur,
        )

        if kunci_waypoint in id_waypoint_diproses:
            return
        id_waypoint_diproses.add(kunci_waypoint)

        kota_target = (
            pengiriman_wp.kota_asal if tipe_wp == "pickup" else pengiriman_wp.kota_tujuan
        )
        truk.status = f"menuju_{tipe_wp}_{pengiriman_wp.id_pengiriman}_s3"

        # Hitung perjalanan ke waypoint
        if truk.lokasi_sekarang != kota_target:
            rute_wp = LayananRute.dapatkan_rute_segmen(
                truk.lokasi_sekarang, kota_target, mode_perutean, hindari_lalu_lintas
            )
            if rute_wp and "summary" in rute_wp:
                if truk.indeks_waypoint_tur == 0:
                    pengiriman_wp.rute_depot_ke_asal_json = rute_wp

                ringkasan_wp = rute_wp["summary"]
                durasi_wp_detik = ringkasan_wp["travelTimeInSeconds"]
                jarak_wp_km = ringkasan_wp["lengthInMeters"] / 1000

                biaya_bbm_wp, biaya_sopir_wp, _ = KalkulatorBiaya.hitung_biaya_segmen(
                    jarak_wp_km, durasi_wp_detik / 3600
                )

                # Bagi biaya ke pengiriman aktif dalam muatan
                pengiriman_aktif = [
                    p_aktif
                    for p_aktif, tipe_aktif in truk.tur_konsolidasi[: truk.indeks_waypoint_tur + 1]
                    if tipe_aktif == "pickup"
                    and p_aktif.muat_selesai
                    and not p_aktif.bongkar_selesai
                ]
                if not pengiriman_aktif and tipe_wp == "pickup":
                    pengiriman_aktif = [pengiriman_wp]

                if pengiriman_aktif:
                    biaya_per_pengiriman = (
                        (biaya_bbm_wp + biaya_sopir_wp) / len(pengiriman_aktif)
                    )
                    for p_aktif in pengiriman_aktif:
                        p_aktif.biaya_pengiriman_total += biaya_per_pengiriman

                truk.total_biaya_bbm += biaya_bbm_wp
                truk.total_biaya_sopir += biaya_sopir_wp
                waktu_aktif += durasi_wp_detik
                truk.total_km_operasional += jarak_wp_km
                truk.total_jam_mengemudi += durasi_wp_detik / 3600
            else:
                # Rute gagal — tandai seluruh sisa tur sebagai gagal
                for p_gagal, _ in truk.tur_konsolidasi[truk.indeks_waypoint_tur:]:
                    if not p_gagal.bongkar_selesai:
                        p_gagal.status_pengiriman = "gagal_tur_rute_s3"
                truk.tur_konsolidasi = []
                truk.status = "siaga_di_depot"
                truk.waktu_event_berikutnya = waktu_aktif
                return

        self._perbarui_lokasi_truk(truk, kota_target)

        if tipe_wp == "pickup":
            pengiriman_wp.waktu_mulai_muat = waktu_aktif
            durasi_muat_detik = pengiriman_wp.estimasi_waktu_muat_menit * 60
            self._proses_muat_selesai(truk, pengiriman_wp, waktu_aktif + durasi_muat_detik)
            waktu_aktif = pengiriman_wp.waktu_selesai_muat
            pengiriman_wp.waktu_keberangkatan = waktu_aktif
            truk.status = f"selesai_muat_{pengiriman_wp.id_pengiriman}_s3"

        elif tipe_wp == "delivery":
            pengiriman_wp.waktu_tiba_tujuan = waktu_aktif
            pengiriman_wp.waktu_mulai_bongkar = waktu_aktif
            durasi_bongkar_detik = pengiriman_wp.estimasi_waktu_bongkar_menit * 60
            self._proses_bongkar_selesai(truk, pengiriman_wp, waktu_aktif + durasi_bongkar_detik)
            waktu_aktif = pengiriman_wp.waktu_selesai_bongkar
            truk.status = f"selesai_bongkar_{pengiriman_wp.id_pengiriman}_s3"

            if pengiriman_wp.muat_selesai:
                # Hitung metrik rute utama menggunakan estimasi internal
                coord_asal = KOTA_KOORDINAT.get(pengiriman_wp.kota_asal)
                coord_tujuan = KOTA_KOORDINAT.get(pengiriman_wp.kota_tujuan)
                if coord_asal and coord_tujuan:
                    pengiriman_wp.jarak_tempuh_km = LayananRute.hitung_jarak_haversine(
                        coord_asal[0], coord_asal[1], coord_tujuan[0], coord_tujuan[1]
                    )
                    pengiriman_wp.rute_utama_json = LayananRute.estimasi_rute_internal(
                        (coord_asal[0], coord_asal[1]),
                        (coord_tujuan[0], coord_tujuan[1]),
                    )

                if (
                    pengiriman_wp.waktu_keberangkatan > 0
                    and pengiriman_wp.waktu_tiba_tujuan > pengiriman_wp.waktu_keberangkatan
                ):
                    pengiriman_wp.estimasi_waktu_tempuh_menit = (
                        (pengiriman_wp.waktu_tiba_tujuan - pengiriman_wp.waktu_keberangkatan)
                        / 60
                    )
                else:
                    pengiriman_wp.estimasi_waktu_tempuh_menit = -1

                hasil_trip.append(KalkulatorBiaya.buat_ringkasan_trip(pengiriman_wp, truk))

        truk.indeks_waypoint_tur += 1
        truk.waktu_event_berikutnya = waktu_aktif

        if truk.indeks_waypoint_tur >= len(truk.tur_konsolidasi):
            truk.status = "menyelesaikan_tur_s3"
        else:
            antrian_event.append(
                (truk.waktu_event_berikutnya, "LANJUT_TUR_S3", truk.id_truk)
            )

    # ─────────────────────────────────────────────────────────────
    # 5.7 DISPATCHER UTAMA
    # ─────────────────────────────────────────────────────────────

    def jalankan_simulasi(
        self,
        jumlah_truk: int,
        jumlah_pengiriman: int,
        durasi_simulasi_hari: int,
        hindari_lalu_lintas: bool,
        nomor_run: int,
        mode_perutean: str,
        mode_distribusi: str,
        skenario_dipilih: str,
        kota_asal_tetap: Optional[str] = None,
        kota_tujuan_tetap: Optional[str] = None,
        string_kota_depot: Optional[str] = None,
    ) -> Tuple[List[Dict], List[Pengiriman], List[Truk], Optional[str], Optional[str]]:
        """
        Titik masuk utama simulasi. Menginisialisasi sistem, memilih skenario,
        menghasilkan visualisasi, dan mengembalikan semua hasil.

        Returns:
            Tuple (hasil_trip, pengiriman_diproses, armada_truk, path_peta_statis, path_peta_dinamis)
        """
        self.inisialisasi_armada(jumlah_truk, string_kota_depot=string_kota_depot)
        self.buat_daftar_pengiriman(
            jumlah_pengiriman,
            durasi_generasi_hari=durasi_simulasi_hari,
            mode_pengiriman=mode_distribusi,
            kota_asal_tetap=kota_asal_tetap,
            kota_tujuan_tetap=kota_tujuan_tetap,
        )

        print(f"\nMemulai Simulasi (Run {nomor_run}) — Skenario: {skenario_dipilih}")
        print(f"  Mode Perutean: {mode_perutean}")

        # Jalankan skenario yang dipilih
        if "Skenario 1" in skenario_dipilih:
            hasil_trip, pengiriman_diproses = self.jalankan_skenario1(
                mode_perutean, hindari_lalu_lintas, nomor_run
            )
        elif "Skenario 2" in skenario_dipilih:
            hasil_trip, pengiriman_diproses = self.jalankan_skenario2(
                mode_perutean, hindari_lalu_lintas, nomor_run
            )
        elif "Skenario 3" in skenario_dipilih:
            hasil_trip, pengiriman_diproses = self.jalankan_skenario3(
                mode_perutean, hindari_lalu_lintas, nomor_run
            )
        else:
            hasil_trip, pengiriman_diproses = self.jalankan_simulasi_dasar(
                mode_perutean, hindari_lalu_lintas, nomor_run
            )

        # Hitung ringkasan statistik
        rangkuman_pengiriman = self._hitung_rangkuman_pengiriman(pengiriman_diproses)
        rangkuman_armada = self._hitung_rangkuman_armada()
        depot_digunakan = list(set(t.lokasi_depot for t in self.armada_truk))

        # Buat visualisasi
        peta_statis = VisualisasiPeta.simpan_peta_statis(
            pengiriman_diproses,
            nomor_run,
            DIREKTORI_SIMPAN,
            depot_digunakan=depot_digunakan,
            rangkuman_pengiriman=rangkuman_pengiriman,
            rangkuman_armada=rangkuman_armada,
        )

        peta_dinamis = self._buat_peta_dinamis(
            pengiriman_diproses, nomor_run,
            rangkuman_pengiriman, rangkuman_armada, depot_digunakan,
        )

        return hasil_trip, pengiriman_diproses, self.armada_truk, peta_statis, peta_dinamis

    def _buat_peta_dinamis(
        self,
        pengiriman_diproses: List[Pengiriman],
        nomor_run: int,
        rangkuman_pengiriman: Dict,
        rangkuman_armada: Dict,
        depot_digunakan: List[str],
    ) -> Optional[str]:
        """Membuat dan menyimpan peta animasi dinamis jika ada data yang valid."""
        pengiriman_selesai = [
            p for p in pengiriman_diproses if p.status_pengiriman.startswith("selesai")
        ]
        if not pengiriman_selesai:
            return None

        df_animasi = VisualisasiPeta.siapkan_data_animasi(
            pengiriman_selesai, LANGKAH_WAKTU_ANIMASI_MENIT
        )
        if df_animasi.empty:
            return None

        warna_palette = px.colors.qualitative.Plotly
        frame_maksimum = df_animasi["frame_id"].max()
        truk_unik = sorted(df_animasi["label_legenda"].unique())
        peta_warna = {t: warna_palette[i % len(warna_palette)] for i, t in enumerate(truk_unik)}

        fig = go.Figure()

        # Tambahkan jejak rute statis
        for p_obj in pengiriman_selesai:
            warna = peta_warna.get(f"Truk {p_obj.id_truk_ditugaskan[-3:]}", "#CCCCCC")

            if p_obj.rute_depot_ke_asal_json and p_obj.rute_depot_ke_asal_json.get("legs"):
                titik_titik = p_obj.rute_depot_ke_asal_json["legs"][0]["points"]
                fig.add_trace(go.Scattergeo(
                    lon=[pt["longitude"] for pt in titik_titik],
                    lat=[pt["latitude"] for pt in titik_titik],
                    mode="lines",
                    line={"width": 1.5, "color": warna, "dash": "dot"},
                    hoverinfo="none",
                    showlegend=False,
                ))

            if p_obj.rute_utama_json and p_obj.rute_utama_json.get("legs"):
                titik_titik = p_obj.rute_utama_json["legs"][0]["points"]
                fig.add_trace(go.Scattergeo(
                    lon=[pt["longitude"] for pt in titik_titik],
                    lat=[pt["latitude"] for pt in titik_titik],
                    mode="lines",
                    line={"width": 2, "color": warna},
                    hoverinfo="none",
                    showlegend=False,
                ))
                fig.add_trace(go.Scattergeo(
                    lon=[titik_titik[0]["longitude"]],
                    lat=[titik_titik[0]["latitude"]],
                    mode="markers",
                    marker={"size": 8, "color": warna, "symbol": "circle"},
                    text=f"Asal: {p_obj.kota_asal}",
                    hoverinfo="text",
                    showlegend=False,
                ))
                fig.add_trace(go.Scattergeo(
                    lon=[titik_titik[-1]["longitude"]],
                    lat=[titik_titik[-1]["latitude"]],
                    mode="markers",
                    marker={"size": 8, "color": warna, "symbol": "star"},
                    text=f"Tujuan: {p_obj.kota_tujuan}",
                    hoverinfo="text",
                    showlegend=False,
                ))

        # Tandai lokasi depot
        if depot_digunakan:
            fig.add_trace(go.Scattergeo(
                lon=[KOTA_KOORDINAT[k][1] for k in depot_digunakan],
                lat=[KOTA_KOORDINAT[k][0] for k in depot_digunakan],
                mode="markers",
                marker={"size": 10, "color": "black", "symbol": "diamond-wide"},
                name="Lokasi Depot",
                hoverinfo="text",
                text=[f"Depot: {k}" for k in depot_digunakan],
            ))

        # Tambahkan trace dinamis truk
        indeks_trace_dinamis = []
        for label_truk in truk_unik:
            df_frame0 = df_animasi[
                (df_animasi["frame_id"] == 0) & (df_animasi["label_legenda"] == label_truk)
            ]
            fig.add_trace(go.Scattergeo(
                lon=df_frame0["longitude"],
                lat=df_frame0["latitude"],
                mode="markers",
                marker={"color": peta_warna[label_truk], "size": 12, "line": {"width": 1.5, "color": "black"}},
                name=label_truk,
                hoverinfo="text",
                text=df_frame0["teks_hover"],
            ))
            indeks_trace_dinamis.append(len(fig.data) - 1)

        # Buat frame animasi
        fig.frames = [
            go.Frame(
                name=str(i),
                traces=indeks_trace_dinamis,
                data=[
                    go.Scattergeo(
                        lon=df_animasi[
                            (df_animasi["frame_id"] == i)
                            & (df_animasi["label_legenda"] == label_truk)
                        ]["longitude"],
                        lat=df_animasi[
                            (df_animasi["frame_id"] == i)
                            & (df_animasi["label_legenda"] == label_truk)
                        ]["latitude"],
                        text=df_animasi[
                            (df_animasi["frame_id"] == i)
                            & (df_animasi["label_legenda"] == label_truk)
                        ]["teks_hover"],
                    )
                    for label_truk in truk_unik
                ],
            )
            for i in range(int(frame_maksimum) + 1)
        ]

        semua_kota = set(depot_digunakan)
        for p in pengiriman_diproses:
            semua_kota.add(p.kota_asal)
            semua_kota.add(p.kota_tujuan)

        VisualisasiPeta.konfigurasi_layout_animasi(fig, frame_maksimum, semua_kota, nomor_run)

        payload_js = {
            "shipments": {
                k: v
                for k, v in VisualisasiPeta.siapkan_event_animasi(pengiriman_diproses).items()
            },
            "summary": {
                "pengiriman": VisualisasiPeta.buat_html_rangkuman_pengiriman(rangkuman_pengiriman),
                "armada": VisualisasiPeta.buat_html_rangkuman_armada(rangkuman_armada),
            },
            "max_frame": int(frame_maksimum),
        }

        return VisualisasiPeta.simpan_peta_dinamis(fig, payload_js, nomor_run, DIREKTORI_SIMPAN)

    # ─────────────────────────────────────────────────────────────
    # 5.8 METODE PEMBANTU UMUM
    # ─────────────────────────────────────────────────────────────

    def _reset_status_armada(self) -> None:
        """Mereset seluruh atribut operasional armada ke kondisi awal (siaga di depot)."""
        for truk in self.armada_truk:
            truk.waktu_event_berikutnya = 0.0
            self._perbarui_lokasi_truk(truk, truk.lokasi_depot)
            truk.status = "siaga_di_depot"
            truk.muatan_saat_ini_ton = 0.0
            truk.jadwal_tugas_statis = []
            truk.tur_konsolidasi = []
            truk.id_pengiriman_aktif = None

    def _reset_truk_untuk_skenario3(self, truk: Truk) -> None:
        """Mereset atribut tambahan yang spesifik untuk Skenario 3."""
        truk.waktu_event_berikutnya = 0.0
        self._perbarui_lokasi_truk(truk, truk.lokasi_depot)
        truk.status = "siaga_di_depot"
        truk.muatan_saat_ini_ton = 0.0
        truk.tur_konsolidasi = []
        truk.indeks_waypoint_tur = 0

    def _pilih_truk_tersedia(
        self, waktu_simulasi: float, berat_ton: float
    ) -> Optional[Truk]:
        """Memilih truk pertama yang siaga dan bisa mengangkut berat yang diberikan."""
        for truk in self.armada_truk:
            if truk.apakah_siaga(waktu_simulasi) and truk.bisa_angkut(berat_ton):
                return truk
        return None

    def _proses_perjalanan_ke_lokasi_muat(
        self,
        truk: Truk,
        pengiriman: Pengiriman,
        waktu_mulai: float,
        mode_perutean: str,
        hindari_lalu_lintas: bool,
    ) -> bool:
        """
        Memproses perjalanan truk dari lokasi sekarang ke lokasi muat pengiriman.
        Mengembalikan True jika berhasil, False jika rute tidak ditemukan.
        """
        rute = LayananRute.dapatkan_rute_segmen(
            truk.lokasi_sekarang, pengiriman.kota_asal, mode_perutean, hindari_lalu_lintas
        )
        if rute and "summary" in rute:
            pengiriman.rute_depot_ke_asal_json = rute
            ringkasan = rute["summary"]
            durasi_detik = ringkasan["travelTimeInSeconds"]
            jarak_km = ringkasan["lengthInMeters"] / 1000
            self._catat_biaya_dan_metrik_mengemudi(
                truk, pengiriman, jarak_km, durasi_detik / 3600
            )
            truk.waktu_event_berikutnya = waktu_mulai + durasi_detik
            self._perbarui_lokasi_truk(truk, pengiriman.kota_asal)
            return True

        pengiriman.status_pengiriman = "gagal_rute_ke_muatan"
        return False

    def _resolve_entitas(
        self,
        data_id: str,
        pengiriman_diproses: List[Pengiriman],
    ) -> Tuple[Optional[Truk], Optional[Pengiriman]]:
        """
        Memetakan ID entitas ke objek Truk atau Pengiriman yang sesuai.
        Mengembalikan tuple (truk, pengiriman) dengan None jika tidak ditemukan.
        """
        truk_event: Optional[Truk] = None
        pengiriman_event: Optional[Pengiriman] = None

        if isinstance(data_id, str) and data_id.startswith("T"):
            truk_event = next(
                (t for t in self.armada_truk if t.id_truk == data_id), None
            )
        elif isinstance(data_id, str) and data_id.startswith("P"):
            pengiriman_event = next(
                (p for p in pengiriman_diproses if p.id_pengiriman == data_id), None
            )
            if pengiriman_event and pengiriman_event.id_truk_ditugaskan:
                truk_event = next(
                    (t for t in self.armada_truk if t.id_truk == pengiriman_event.id_truk_ditugaskan),
                    None,
                )

        return truk_event, pengiriman_event

    def _hitung_rangkuman_pengiriman(
        self, pengiriman_diproses: List[Pengiriman]
    ) -> Dict[str, int]:
        """Menghitung statistik penyelesaian pengiriman (tepat waktu, terlambat, gagal)."""
        rangkuman: Dict[str, int] = defaultdict(int)
        for p in pengiriman_diproses:
            if p.status_pengiriman == "selesai":
                rangkuman["tepat_waktu"] += 1
            elif p.status_pengiriman == "selesai_terlambat":
                rangkuman["terlambat"] += 1
            else:
                rangkuman["gagal"] += 1
        return rangkuman

    def _hitung_rangkuman_armada(self) -> Dict[str, int]:
        """Menghitung statistik operasional armada (beroperasi vs menganggur)."""
        rangkuman: Dict[str, int] = defaultdict(int)
        for truk in self.armada_truk:
            if truk.jumlah_trip_selesai > 0:
                rangkuman["beroperasi"] += 1
            else:
                rangkuman["menganggur"] += 1
        return rangkuman


# =============================================================================
# BAGIAN 6 — VISUALISASI PETA (Statis & Dinamis)
# =============================================================================

class VisualisasiPeta:
    """
    Menyediakan semua fungsi untuk menghasilkan file HTML visualisasi peta:
    - Peta rute statis (Plotly Scattergeo)
    - Peta animasi dinamis dengan panel log (Plotly + JavaScript)
    """

    # ─────────────────────────────────────────────────────────────
    # 6.1 PETA STATIS
    # ─────────────────────────────────────────────────────────────

    @staticmethod
    def simpan_peta_statis(
        pengiriman_diproses: List[Pengiriman],
        nomor_run: int,
        direktori_simpan: str,
        awalan_nama_file: str = "Visualisasi_Rute_Statis",
        depot_digunakan: Optional[List[str]] = None,
        rangkuman_pengiriman: Optional[Dict] = None,
        rangkuman_armada: Optional[Dict] = None,
    ) -> Optional[str]:
        """Membuat dan menyimpan peta rute statis dalam format HTML."""
        os.makedirs(direktori_simpan, exist_ok=True)
        nama_file = f"{awalan_nama_file}_{nomor_run}.html"
        path_file = os.path.join(direktori_simpan, nama_file)

        fig = go.Figure()
        warna_palette = px.colors.qualitative.Plotly
        anotasi = []

        # Tandai depot
        if depot_digunakan:
            lat_depot = [KOTA_KOORDINAT[k][0] for k in depot_digunakan if k in KOTA_KOORDINAT]
            lon_depot = [KOTA_KOORDINAT[k][1] for k in depot_digunakan if k in KOTA_KOORDINAT]
            teks_depot = [f"Depot: {k}" for k in depot_digunakan if k in KOTA_KOORDINAT]
            fig.add_trace(go.Scattergeo(
                lon=lon_depot,
                lat=lat_depot,
                mode="markers",
                marker={"size": 12, "color": "black", "symbol": "diamond-wide",
                        "line": {"width": 1, "color": "white"}},
                name="Lokasi Depot",
                hoverinfo="text",
                text=teks_depot,
            ))

        rute_untuk_plot = [
            p for p in pengiriman_diproses if p.status_pengiriman.startswith("selesai")
        ]
        if not rute_untuk_plot and not depot_digunakan:
            print("Tidak ada rute valid untuk visualisasi statis.")
            return None

        semua_lintang: List[float] = []
        semua_bujur: List[float] = []
        semua_kota: set = set(depot_digunakan if depot_digunakan else [])

        for idx, p_obj in enumerate(rute_untuk_plot):
            semua_kota.add(p_obj.kota_asal)
            semua_kota.add(p_obj.kota_tujuan)
            warna = warna_palette[idx % len(warna_palette)]

            if p_obj.rute_depot_ke_asal_json and p_obj.rute_depot_ke_asal_json.get("legs"):
                rute_d = p_obj.rute_depot_ke_asal_json
                if rute_d["legs"][0]["points"]:
                    titik = rute_d["legs"][0]["points"]
                    lats = [pt["latitude"] for pt in titik]
                    lons = [pt["longitude"] for pt in titik]
                    semua_lintang.extend(lats)
                    semua_bujur.extend(lons)
                    fig.add_trace(go.Scattergeo(
                        lon=lons, lat=lats, mode="lines",
                        line={"width": 2, "color": warna, "dash": "dash"},
                        showlegend=False, hoverinfo="none",
                    ))

            if p_obj.rute_utama_json and p_obj.rute_utama_json.get("legs"):
                rute_u = p_obj.rute_utama_json
                if rute_u["legs"][0]["points"]:
                    titik = rute_u["legs"][0]["points"]
                    lats = [pt["latitude"] for pt in titik]
                    lons = [pt["longitude"] for pt in titik]
                    semua_lintang.extend(lats)
                    semua_bujur.extend(lons)

                    teks_legenda = (
                        f"Truk {p_obj.id_truk_ditugaskan[-3:]} "
                        f"({p_obj.kota_asal} ke {p_obj.kota_tujuan})"
                    )
                    fig.add_trace(go.Scattergeo(
                        lon=lons, lat=lats, mode="lines",
                        line={"width": 3, "color": warna},
                        name=teks_legenda, hoverinfo="none",
                        legendgroup=p_obj.id_pengiriman,
                    ))
                    fig.add_trace(go.Scattergeo(
                        lon=[lons[0]], lat=[lats[0]], mode="markers",
                        marker={"size": 10, "color": warna, "symbol": "circle"},
                        text=f"Asal: {p_obj.kota_asal}", hoverinfo="text",
                        name=f"Asal: {p_obj.kota_asal}",
                        showlegend=False, legendgroup=p_obj.id_pengiriman,
                    ))
                    fig.add_trace(go.Scattergeo(
                        lon=[lons[-1]], lat=[lats[-1]], mode="markers",
                        marker={"size": 10, "color": warna, "symbol": "star"},
                        text=f"Tujuan: {p_obj.kota_tujuan}", hoverinfo="text",
                        name=f"Tujuan: {p_obj.kota_tujuan}",
                        showlegend=False, legendgroup=p_obj.id_pengiriman,
                    ))

        if rangkuman_pengiriman and rangkuman_armada:
            teks_rangkuman = (
                f"<b>Rangkuman Simulasi Ke-{nomor_run}</b><br><br>"
                f"<b>Pengiriman:</b><br>"
                f"  Tepat Waktu: {rangkuman_pengiriman.get('tepat_waktu', 0)}<br>"
                f"  Terlambat: {rangkuman_pengiriman.get('terlambat', 0)}<br>"
                f"  Gagal: {rangkuman_pengiriman.get('gagal', 0)}<br><br>"
                f"<b>Armada:</b><br>"
                f"  Beroperasi: {rangkuman_armada.get('beroperasi', 0)}<br>"
                f"  Menganggur: {rangkuman_armada.get('menganggur', 0)}"
            )
            anotasi.append({
                "x": 0.01, "y": 0.99, "xref": "paper", "yref": "paper",
                "text": teks_rangkuman, "showarrow": False, "align": "left",
                "font": {"size": 12, "color": "black"},
                "bgcolor": "rgba(255, 255, 240, 0.88)",
                "bordercolor": "black", "borderwidth": 1,
            })

        batas_lat, batas_lon, pusat_lat, pusat_lon = VisualisasiPeta._hitung_zoom_peta(semua_kota)

        fig.update_layout(
            title=f"Peta Rute Pengiriman (Statis) — Simulasi Ke-{nomor_run}",
            annotations=anotasi,
            geo={
                "scope": "asia",
                "projection_type": "mercator",
                "center": {"lat": pusat_lat, "lon": pusat_lon},
                "showland": True,
                "landcolor": "rgb(220, 220, 220)",
                "countrycolor": "rgb(200, 200, 200)",
                "lataxis_range": batas_lat,
                "lonaxis_range": batas_lon,
                "subunitcolor": "grey",
            },
            hovermode="closest",
            legend_title_text="Legenda Pengiriman",
            legend={
                "orientation": "v", "yanchor": "top", "y": 1,
                "xanchor": "right", "x": 1.15,
            },
        )

        try:
            fig.write_html(path_file)
            return path_file
        except Exception:  # pylint: disable=broad-except
            print(f"Error menyimpan peta statis:")
            print(traceback.format_exc())
            return None

    # ─────────────────────────────────────────────────────────────
    # 6.2 DATA ANIMASI
    # ─────────────────────────────────────────────────────────────

    @staticmethod
    def _buat_frame_animasi_segmen(
        data_rute: Dict,
        waktu_mulai_menit: float,
        langkah_waktu_menit: int,
        label_legenda: str,
        teks_hover: str,
    ) -> List[Dict]:
        """
        Menghasilkan daftar frame posisi truk untuk satu segmen perjalanan.
        Menginterpolasi posisi berdasarkan waktu tempuh proporsional.
        """
        frame_segmen: List[Dict] = []

        kondisi_tidak_valid = not (
            data_rute
            and "legs" in data_rute
            and data_rute["legs"]
            and "points" in data_rute["legs"][0]
            and data_rute["legs"][0]["points"]
        )
        if kondisi_tidak_valid:
            return []

        titik_titik = data_rute["legs"][0]["points"]
        total_waktu_detik = data_rute["summary"]["travelTimeInSeconds"]
        if total_waktu_detik <= 0:
            return []

        total_waktu_menit = total_waktu_detik / 60
        total_jarak_km = data_rute["summary"]["lengthInMeters"] / 1000

        # Hitung waktu kumulatif tiap segmen titik
        waktu_kumulatif = [0.0]
        if total_jarak_km > 0 and len(titik_titik) > 1:
            jarak_saat_ini = 0.0
            for j in range(1, len(titik_titik)):
                jarak_seg = LayananRute.hitung_jarak_haversine(
                    titik_titik[j - 1]["latitude"], titik_titik[j - 1]["longitude"],
                    titik_titik[j]["latitude"], titik_titik[j]["longitude"],
                )
                jarak_saat_ini += jarak_seg
                waktu_seg_menit = (jarak_seg / total_jarak_km) * total_waktu_menit
                waktu_kumulatif.append(waktu_kumulatif[-1] + waktu_seg_menit)
        else:
            n_titik = max(len(titik_titik), 2)
            waktu_kumulatif = np.linspace(0, total_waktu_menit, n_titik).tolist()

        # Normalisasi skala waktu
        if waktu_kumulatif[-1] > 0:
            faktor_skala = total_waktu_menit / waktu_kumulatif[-1]
            waktu_kumulatif = [t * faktor_skala for t in waktu_kumulatif]

        waktu_relatif = 0.0
        waktu_relatif_maks = total_waktu_menit

        while True:
            waktu_global_menit = waktu_mulai_menit + waktu_relatif

            if waktu_relatif >= waktu_relatif_maks:
                lat_interp = titik_titik[-1]["latitude"]
                lon_interp = titik_titik[-1]["longitude"]
            else:
                idx = np.searchsorted(waktu_kumulatif, waktu_relatif, side="right")
                idx = min(idx, len(titik_titik) - 1)
                idx0 = max(0, idx - 1)

                selisih_waktu = waktu_kumulatif[idx] - waktu_kumulatif[idx0]
                if selisih_waktu > 0:
                    rasio = (waktu_relatif - waktu_kumulatif[idx0]) / selisih_waktu
                else:
                    rasio = 0.0
                rasio = max(0.0, min(1.0, rasio))

                lat_interp = (
                    titik_titik[idx0]["latitude"]
                    + (titik_titik[idx]["latitude"] - titik_titik[idx0]["latitude"]) * rasio
                )
                lon_interp = (
                    titik_titik[idx0]["longitude"]
                    + (titik_titik[idx]["longitude"] - titik_titik[idx0]["longitude"]) * rasio
                )

            frame_segmen.append({
                "label_legenda": label_legenda,
                "latitude": lat_interp,
                "longitude": lon_interp,
                "waktu_sim_menit": waktu_global_menit,
                "teks_hover": teks_hover,
            })

            if waktu_relatif >= waktu_relatif_maks:
                break
            waktu_relatif += langkah_waktu_menit
            waktu_relatif = min(waktu_relatif, waktu_relatif_maks)

        return frame_segmen

    @staticmethod
    def siapkan_data_animasi(
        pengiriman_diproses: List[Pengiriman],
        langkah_waktu_menit: int = LANGKAH_WAKTU_ANIMASI_MENIT,
    ) -> pd.DataFrame:
        """
        Menyiapkan DataFrame berisi posisi truk per frame waktu untuk animasi Plotly.
        Menggabungkan segmen perjalanan depot-ke-asal dan asal-ke-tujuan.
        """
        semua_frame: List[Dict] = []

        for p_obj in pengiriman_diproses:
            if not p_obj.status_pengiriman.startswith("selesai"):
                continue

            label_anim = f"Truk {p_obj.id_truk_ditugaskan[-3:]}"
            teks_hover = (
                f"Truk {p_obj.id_truk_ditugaskan[-3:]}; "
                f"{p_obj.id_pengiriman}; "
                f"{p_obj.kota_asal} → {p_obj.kota_tujuan}"
            )

            if p_obj.rute_depot_ke_asal_json:
                waktu_mulai_kaki1 = (
                    p_obj.waktu_truk_dialokasikan / 60
                    if p_obj.waktu_truk_dialokasikan > 0
                    else 0.0
                )
                frame_kaki1 = VisualisasiPeta._buat_frame_animasi_segmen(
                    p_obj.rute_depot_ke_asal_json, waktu_mulai_kaki1,
                    langkah_waktu_menit, label_anim, teks_hover,
                )
                semua_frame.extend(frame_kaki1)

            if p_obj.rute_utama_json:
                waktu_mulai_kaki2 = (
                    p_obj.waktu_keberangkatan / 60
                    if p_obj.waktu_keberangkatan > 0
                    else p_obj.waktu_mulai_muat / 60
                )
                frame_kaki2 = VisualisasiPeta._buat_frame_animasi_segmen(
                    p_obj.rute_utama_json, waktu_mulai_kaki2,
                    langkah_waktu_menit, label_anim, teks_hover,
                )
                semua_frame.extend(frame_kaki2)

        if not semua_frame:
            return pd.DataFrame()

        df = pd.DataFrame(semua_frame)
        df["frame_id"] = (df["waktu_sim_menit"] / langkah_waktu_menit).round().astype(int)
        df = df.sort_values("waktu_sim_menit")
        df = df.drop_duplicates(subset=["frame_id", "label_legenda"], keep="last")
        return df.sort_values(by=["frame_id", "label_legenda"]).reset_index(drop=True)

    # ─────────────────────────────────────────────────────────────
    # 6.3 PETA DINAMIS DENGAN LOG
    # ─────────────────────────────────────────────────────────────

    @staticmethod
    def siapkan_event_animasi(
        pengiriman_diproses: List[Pengiriman],
    ) -> defaultdict:
        """
        Menyiapkan dict event log per frame animasi.
        Setiap pengiriman dipetakan ke frame berdasarkan waktu penyelesaian atau
        waktu permintaan dibuat (untuk yang gagal).
        """
        event_animasi: defaultdict = defaultdict(list)

        for p in pengiriman_diproses:
            waktu_event_detik = 0.0
            if p.waktu_penyelesaian_aktual > 0:
                waktu_event_detik = p.waktu_penyelesaian_aktual
            elif p.status_pengiriman != "menunggu_alokasi_truk":
                waktu_event_detik = p.waktu_permintaan_dibuat

            id_frame = int(round(
                (waktu_event_detik / 60) / LANGKAH_WAKTU_ANIMASI_MENIT
            ))

            teks_status, warna_hex, kelas_css = VisualisasiPeta._dapatkan_info_status(
                p.status_pengiriman
            )
            if p.status_pengiriman.startswith("selesai"):
                pesan = (
                    f"<strong>{p.id_pengiriman}:</strong> "
                    f"{p.kota_asal} → {p.kota_tujuan} "
                    f"<span style='color:{warna_hex}; font-weight:bold;'>"
                    f"({teks_status})</span>"
                )
            else:
                pesan = (
                    f"<strong>{p.id_pengiriman}:</strong> "
                    f"Status <span style='color:{warna_hex}; font-weight:bold;'>"
                    f"({teks_status})</span>"
                )

            event_animasi[id_frame].append({
                "message": pesan,
                "css_class": kelas_css,
            })

        return event_animasi

    @staticmethod
    def _dapatkan_info_status(status_str: str) -> Tuple[str, str, str]:
        """
        Mengembalikan (teks_tampilan, warna_hex, kelas_css) berdasarkan string status.
        """
        if status_str == "selesai":
            return "Tepat Waktu", "#1e8e3e", "log-tepat-waktu"
        if status_str == "selesai_terlambat":
            return "Terlambat", "#e37400", "log-terlambat"
        teks = status_str.replace("_", " ").title()
        return teks, "#c62828", "log-gagal"

    @staticmethod
    def konfigurasi_layout_animasi(
        fig: go.Figure,
        frame_maksimum: float,
        semua_kota: set,
        nomor_run: int,
    ) -> None:
        """Mengatur layout dan kontrol animasi (slider, play/pause) pada figur Plotly."""
        batas_lat, batas_lon, pusat_lat, pusat_lon = VisualisasiPeta._hitung_zoom_peta(semua_kota)

        fig.update_layout(
            title=f"Visualisasi Animasi Pengiriman — Simulasi Ke-{nomor_run}",
            updatemenus=[{
                "type": "buttons",
                "direction": "right",
                "x": 0.6,
                "y": 1.1,
                "buttons": [
                    {
                        "label": "▶ Play",
                        "method": "animate",
                        "args": [
                            [None],
                            {"frame": {"duration": 200, "redraw": True},
                             "fromcurrent": True,
                             "transition": {"duration": 100}},
                        ],
                    },
                    {
                        "label": "⏸ Pause",
                        "method": "animate",
                        "args": [
                            [None],
                            {"frame": {"duration": 0, "redraw": False}, "mode": "immediate"},
                        ],
                    },
                ],
            }],
            sliders=[{
                "active": 0,
                "currentvalue": {"prefix": "Waktu Simulasi: "},
                "pad": {"t": 50},
                "steps": [
                    {
                        "label": (
                            f"H{int((i * LANGKAH_WAKTU_ANIMASI_MENIT) // (24 * 60))} "
                            f"{int(((i * LANGKAH_WAKTU_ANIMASI_MENIT) % (24 * 60)) // 60):02d}:"
                            f"{int((i * LANGKAH_WAKTU_ANIMASI_MENIT) % 60):02d}"
                        ),
                        "method": "animate",
                        "args": [
                            [str(i)],
                            {"frame": {"duration": 200, "redraw": False}, "mode": "immediate"},
                        ],
                    }
                    for i in range(int(frame_maksimum) + 1)
                ],
            }],
            legend={
                "traceorder": "grouped", "orientation": "h",
                "yanchor": "bottom", "y": 1.02, "xanchor": "right", "x": 1,
            },
            geo={
                "scope": "asia",
                "center": {"lat": pusat_lat, "lon": pusat_lon},
                "lataxis_range": batas_lat,
                "lonaxis_range": batas_lon,
                "projection_type": "mercator",
                "showland": True,
                "landcolor": "rgb(220, 220, 220)",
            },
        )

    @staticmethod
    def buat_html_rangkuman_pengiriman(rangkuman: Dict) -> str:
        """Membuat HTML ringkasan pengiriman untuk panel log animasi."""
        tepat = rangkuman.get("tepat_waktu", 0)
        terlambat = rangkuman.get("terlambat", 0)
        gagal = rangkuman.get("gagal", 0)
        total = tepat + terlambat + gagal
        return (
            f'<div class="baris-statistik">'
            f'<span>Tepat Waktu</span>'
            f'<span class="nilai nilai-sukses">{tepat}/{total}</span>'
            f'</div>'
            f'<div class="baris-statistik">'
            f'<span>Terlambat</span>'
            f'<span class="nilai nilai-peringatan">{terlambat}/{total}</span>'
            f'</div>'
            f'<div class="baris-statistik">'
            f'<span>Gagal/Tidak Terproses</span>'
            f'<span class="nilai nilai-bahaya">{gagal}/{total}</span>'
            f'</div>'
        )

    @staticmethod
    def buat_html_rangkuman_armada(rangkuman: Dict) -> str:
        """Membuat HTML ringkasan armada untuk panel log animasi."""
        beroperasi = rangkuman.get("beroperasi", 0)
        menganggur = rangkuman.get("menganggur", 0)
        return (
            f'<div class="baris-statistik">'
            f'<span>Truk Beroperasi</span>'
            f'<span class="nilai nilai-sukses">{beroperasi}</span>'
            f'</div>'
            f'<div class="baris-statistik">'
            f'<span>Truk Menganggur</span>'
            f'<span class="nilai nilai-bahaya">{menganggur}</span>'
            f'</div>'
        )

    @staticmethod
    def simpan_peta_dinamis(
        fig: go.Figure,
        payload_js: Dict,
        nomor_run: int,
        direktori_simpan: str,
        awalan_nama_file: str = "Visualisasi_Animasi_Dinamis",
    ) -> Optional[str]:
        """
        Menyimpan peta animasi dinamis dengan panel log pengiriman real-time
        sebagai file HTML mandiri yang profesional.
        """
        os.makedirs(direktori_simpan, exist_ok=True)
        path_file = os.path.join(direktori_simpan, f"{awalan_nama_file}_{nomor_run}.html")

        json_event = json.dumps(payload_js)
        div_plotly = fig.to_html(full_html=False, include_plotlyjs="cdn", div_id="plotly-div")

        html_akhir = f"""<!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Simulasi Logistik — Animasi Run #{nomor_run}</title>
    <style>
        /* ===== DESIGN TOKENS ===== */
        :root {{
            --warna-primer:        #1a73e8;
            --warna-primer-gelap:  #1558b0;
            --warna-sukses:        #1e8e3e;
            --warna-peringatan:    #e37400;
            --warna-bahaya:        #c62828;
            --warna-teks-utama:    #202124;
            --warna-teks-sekunder: #5f6368;
            --warna-latar:         #f8f9fa;
            --warna-panel:         #ffffff;
            --warna-batas:         #dadce0;
            --radius-kartu:        8px;
            --bayangan-sm:         0 1px 3px rgba(0,0,0,0.12);
            --bayangan-md:         0 3px 6px rgba(0,0,0,0.16);
        }}

        /* ===== RESET & BASE ===== */
        *, *::before, *::after {{
            box-sizing: border-box;
            margin: 0;
            padding: 0;
        }}

        html, body {{
            height: 100%;
            width: 100%;
            font-family: 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            font-size: 13px;
            line-height: 1.5;
            color: var(--warna-teks-utama);
            background: var(--warna-latar);
            overflow: hidden;
        }}

        /* ===== LAYOUT UTAMA ===== */
        #tata-letak-utama {{
            display: flex;
            flex-direction: column;
            height: 100vh;
        }}

        /* ===== HEADER ===== */
        #header-aplikasi {{
            flex-shrink: 0;
            display: flex;
            align-items: center;
            justify-content: space-between;
            padding: 0 20px;
            height: 52px;
            background: linear-gradient(135deg, #1a237e 0%, #1565c0 100%);
            color: #ffffff;
            box-shadow: 0 2px 8px rgba(0,0,0,0.3);
            z-index: 10;
        }}

        #header-aplikasi .judul-aplikasi {{
            font-size: 15px;
            font-weight: 600;
            letter-spacing: 0.3px;
            display: flex;
            align-items: center;
            gap: 10px;
        }}

        #header-aplikasi .judul-aplikasi::before {{
            content: '🗺';
            font-size: 18px;
        }}

        #header-aplikasi .lencana-run {{
            background: rgba(255,255,255,0.18);
            border: 1px solid rgba(255,255,255,0.3);
            padding: 4px 14px;
            border-radius: 20px;
            font-size: 12px;
            font-weight: 500;
            letter-spacing: 0.2px;
        }}

        /* ===== AREA KONTEN ===== */
        #area-konten {{
            flex: 1;
            display: flex;
            overflow: hidden;
        }}

        /* ===== PETA ===== */
        #area-peta {{
            flex: 1;
            min-width: 0;
            height: 100%;
        }}

        #plotly-div {{
            width: 100%;
            height: 100%;
        }}

        /* ===== PANEL SAMPING ===== */
        #panel-samping {{
            width: 340px;
            flex-shrink: 0;
            display: flex;
            flex-direction: column;
            background: var(--warna-panel);
            border-left: 1px solid var(--warna-batas);
            box-shadow: -2px 0 8px rgba(0,0,0,0.06);
        }}

        /* Header panel */
        #panel-samping-header {{
            flex-shrink: 0;
            padding: 14px 16px 10px;
            border-bottom: 1px solid var(--warna-batas);
            background: var(--warna-panel);
        }}

        .judul-panel {{
            font-size: 13px;
            font-weight: 600;
            color: var(--warna-teks-utama);
            display: flex;
            align-items: center;
            gap: 8px;
        }}

        .aksen-panel {{
            width: 3px;
            height: 15px;
            background: var(--warna-primer);
            border-radius: 2px;
            display: inline-block;
            flex-shrink: 0;
        }}

        /* Area log bergulir */
        #area-log {{
            flex: 1;
            overflow-y: auto;
            padding: 10px 12px;
            scroll-behavior: smooth;
        }}

        /* ===== ENTRI LOG ===== */
        .entri-log {{
            padding: 9px 11px;
            margin-bottom: 6px;
            border-radius: 5px;
            font-size: 12px;
            line-height: 1.55;
            border-left: 3px solid var(--warna-batas);
            background: var(--warna-latar);
            animation: geser-masuk 0.25s ease-out both;
        }}

        @keyframes geser-masuk {{
            from {{ opacity: 0; transform: translateX(12px); }}
            to   {{ opacity: 1; transform: translateX(0); }}
        }}

        .log-tepat-waktu {{
            background: #e8f5e9;
            border-left-color: #2e7d32;
        }}

        .log-terlambat {{
            background: #fff3e0;
            border-left-color: #e65100;
        }}

        .log-gagal {{
            background: #ffebee;
            border-left-color: #b71c1c;
        }}

        /* ===== PANEL RANGKUMAN ===== */
        #panel-rangkuman {{
            flex-shrink: 0;
            padding: 14px 16px;
            border-top: 1px solid var(--warna-batas);
            background: var(--warna-panel);
            display: none;
        }}

        .judul-rangkuman {{
            font-size: 12px;
            font-weight: 700;
            text-transform: uppercase;
            letter-spacing: 0.6px;
            color: var(--warna-teks-sekunder);
            margin-bottom: 10px;
            display: flex;
            align-items: center;
            gap: 6px;
        }}

        .judul-rangkuman::before {{
            content: '✓';
            width: 16px;
            height: 16px;
            background: var(--warna-sukses);
            color: #fff;
            border-radius: 50%;
            font-size: 10px;
            display: flex;
            align-items: center;
            justify-content: center;
            flex-shrink: 0;
        }}

        .kartu-statistik {{
            background: var(--warna-latar);
            border: 1px solid var(--warna-batas);
            border-radius: var(--radius-kartu);
            padding: 10px 12px;
            margin-bottom: 8px;
        }}

        .label-kartu {{
            font-size: 10px;
            font-weight: 700;
            text-transform: uppercase;
            letter-spacing: 0.7px;
            color: var(--warna-teks-sekunder);
            margin-bottom: 6px;
        }}

        .baris-statistik {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            font-size: 12px;
            padding: 2px 0;
        }}

        .nilai {{ font-weight: 600; }}
        .nilai-sukses   {{ color: var(--warna-sukses); }}
        .nilai-peringatan {{ color: var(--warna-peringatan); }}
        .nilai-bahaya   {{ color: var(--warna-bahaya); }}

        /* ===== SCROLLBAR ===== */
        #area-log::-webkit-scrollbar {{
            width: 4px;
        }}
        #area-log::-webkit-scrollbar-track {{
            background: transparent;
        }}
        #area-log::-webkit-scrollbar-thumb {{
            background: var(--warna-batas);
            border-radius: 2px;
        }}
    </style>
</head>
<body>
<div id="tata-letak-utama">

    <!-- HEADER -->
    <header id="header-aplikasi">
        <div class="judul-aplikasi">Simulasi Logistik Transportasi Truk Nasional</div>
        <span class="lencana-run">Run #{nomor_run}</span>
    </header>

    <!-- KONTEN UTAMA -->
    <div id="area-konten">

        <!-- PETA PLOTLY -->
        <div id="area-peta">
            {div_plotly}
        </div>

        <!-- PANEL LOG SAMPING -->
        <aside id="panel-samping">
            <div id="panel-samping-header">
                <div class="judul-panel">
                    <span class="aksen-panel"></span>
                    Log Status Pengiriman
                </div>
            </div>

            <div id="area-log" role="log" aria-live="polite"></div>

            <div id="panel-rangkuman">
                <div class="judul-rangkuman">Rangkuman Simulasi</div>
                <div class="kartu-statistik">
                    <div class="label-kartu">Pengiriman</div>
                    <div id="isi-rangkuman-pengiriman"></div>
                </div>
                <div class="kartu-statistik">
                    <div class="label-kartu">Armada Truk</div>
                    <div id="isi-rangkuman-armada"></div>
                </div>
            </div>
        </aside>

    </div><!-- /#area-konten -->
</div><!-- /#tata-letak-utama -->

<script type="text/javascript">
    /* ================================================================
     * DATA SIMULASI
     * ================================================================ */
    const DATA_ANIMASI = {json_event};
    const FRAME_MAKSIMUM = DATA_ANIMASI.max_frame;

    /* ================================================================
     * FUNGSI RENDER PANEL LOG
     * ================================================================ */
    function tampilkanRangkuman() {{
        const panelRangkuman = document.getElementById('panel-rangkuman');
        document.getElementById('isi-rangkuman-pengiriman').innerHTML =
            DATA_ANIMASI.summary.pengiriman;
        document.getElementById('isi-rangkuman-armada').innerHTML =
            DATA_ANIMASI.summary.armada;
        panelRangkuman.style.display = 'block';
    }}

    function tambahEntrLog(eventData) {{
        const areaLog = document.getElementById('area-log');
        const elemen = document.createElement('div');
        elemen.innerHTML = eventData.message;
        elemen.className = 'entri-log ' + eventData.css_class;
        areaLog.appendChild(elemen);
    }}

    function gulirKeIntiLogJikaPerlu(areaLog) {{
        const sudahDiBawah =
            areaLog.scrollTop + areaLog.clientHeight >= areaLog.scrollHeight - 60;
        if (sudahDiBawah) {{
            areaLog.scrollTop = areaLog.scrollHeight;
        }}
    }}

    /* ================================================================
     * PENGATUR LOG DINAMIS (Event Listener Plotly)
     * ================================================================ */
    function aturLogDinamis() {{
        const elemenPeta = document.getElementById('plotly-div');
        if (!elemenPeta) {{
            console.error('[SimulasiLogistik] Elemen peta tidak ditemukan.');
            return;
        }}

        const areaLog       = document.getElementById('area-log');
        const frameDiproses = new Set();

        elemenPeta.on('plotly_afterplot', function () {{
            try {{
                if (!elemenPeta.layout || !elemenPeta.layout.sliders) return;

                const nomorFrame = elemenPeta.layout.sliders[0].active;

                // Tambahkan log untuk setiap frame yang belum diproses
                for (let i = 0; i <= nomorFrame; i++) {{
                    if (!frameDiproses.has(i) && DATA_ANIMASI.shipments[i]) {{
                        DATA_ANIMASI.shipments[i].forEach(tambahEntrLog);
                        frameDiproses.add(i);
                    }}
                }}

                gulirKeIntiLogJikaPerlu(areaLog);

                // Tampilkan rangkuman di frame terakhir
                if (nomorFrame === FRAME_MAKSIMUM) {{
                    tampilkanRangkuman();
                }}
            }} catch (err) {{
                console.error('[SimulasiLogistik] Error di plotly_afterplot:', err);
            }}
        }});

        // Panggil sekali di awal untuk frame 0
        setTimeout(function () {{
            if (elemenPeta.emit) elemenPeta.emit('plotly_afterplot');
        }}, 600);
    }}

    window.addEventListener('load', aturLogDinamis);
</script>
</body>
</html>"""

        try:
            with open(path_file, "w", encoding="utf-8") as berkas:
                berkas.write(html_akhir)
            return path_file
        except Exception:  # pylint: disable=broad-except
            print("Error menyimpan peta dinamis:")
            print(traceback.format_exc())
            return None

    # ─────────────────────────────────────────────────────────────
    # 6.4 HELPER ZOOM PETA
    # ─────────────────────────────────────────────────────────────

    @staticmethod
    def _hitung_zoom_peta(
        semua_kota: set,
    ) -> Tuple[List[float], List[float], float, float]:
        """
        Menghitung batas dan pusat peta berdasarkan kota-kota yang terlibat.
        Mengembalikan (batas_lat, batas_lon, pusat_lat, pusat_lon).
        """
        pulau_terlibat = {
            KOTA_KOORDINAT[kota][2]
            for kota in semua_kota
            if kota in KOTA_KOORDINAT
        }

        if len(pulau_terlibat) == 1:
            pulau = pulau_terlibat.pop()
            batas = BATAS_WILAYAH.get(pulau, BATAS_WILAYAH["Indonesia"])
        else:
            batas = BATAS_WILAYAH["Indonesia"]

        batas_lat = batas["lat"]
        batas_lon = batas["lon"]
        pusat_lat = sum(batas_lat) / 2
        pusat_lon = sum(batas_lon) / 2
        return batas_lat, batas_lon, pusat_lat, pusat_lon


# =============================================================================
# BAGIAN 7 — ANTARMUKA PENGGUNA (tkinter GUI)
# =============================================================================

class SimulasiApp(tk.Tk):
    """
    Antarmuka pengguna grafis berbasis tkinter untuk menjalankan simulasi
    logistik. Seluruh eksekusi simulasi berjalan di thread terpisah untuk
    mencegah GUI membeku (freeze).
    """

    # Palet warna antarmuka
    WARNA_HEADER_BG: str  = "#1a237e"
    WARNA_HEADER_FG: str  = "#ffffff"
    WARNA_AKSEN: str      = "#1565c0"
    WARNA_SUKSES: str     = "#2e7d32"
    WARNA_PERINGATAN: str = "#e65100"
    WARNA_BAHAYA: str     = "#c62828"
    WARNA_LATAR: str      = "#f5f5f5"
    WARNA_PANEL: str      = "#ffffff"
    WARNA_TEKS_LOG: str   = "#37474f"
    FONT_MONO: str        = "Courier New"
    FONT_UI: str          = "Segoe UI"

    def __init__(self):
        super().__init__()
        self.title("Simulasi Sistem Transportasi Truk Nasional — v4.0")
        self.geometry("1280x900")
        self.resizable(True, True)
        self.nomor_run_simulasi: int = 0

        # Font kustom
        self.font_judul = tkFont.Font(family=self.FONT_UI, size=11, weight="bold")
        self.font_normal = tkFont.Font(family=self.FONT_UI, size=10)
        self.font_kecil = tkFont.Font(family=self.FONT_UI, size=9)
        self.font_log = tkFont.Font(family=self.FONT_MONO, size=10)
        self.option_add("*Font", self.font_normal)

        self._terapkan_tema()
        self._buat_widget()

    def _terapkan_tema(self) -> None:
        """Mengatur tema ttk untuk tampilan yang lebih profesional."""
        style = ttk.Style(self)
        tema_tersedia = style.theme_names()
        if "clam" in tema_tersedia:
            style.theme_use("clam")
        elif "vista" in tema_tersedia:
            style.theme_use("vista")

        # Tombol aksen (biru)
        style.configure(
            "Aksen.TButton",
            foreground="white",
            background=self.WARNA_AKSEN,
            font=(self.FONT_UI, 10, "bold"),
            padding=(12, 6),
        )
        style.map(
            "Aksen.TButton",
            background=[("active", self.WARNA_HEADER_BG), ("disabled", "#9e9e9e")],
            foreground=[("disabled", "#e0e0e0")],
        )

        # Label frame berornamen
        style.configure(
            "Kartu.TLabelframe",
            background=self.WARNA_PANEL,
            relief="flat",
            borderwidth=1,
        )
        style.configure(
            "Kartu.TLabelframe.Label",
            font=(self.FONT_UI, 9, "bold"),
            foreground=self.WARNA_AKSEN,
        )

        # Notebook tab
        style.configure(
            "TNotebook.Tab",
            padding=(12, 6),
            font=(self.FONT_UI, 9, "bold"),
        )

    def _buat_widget(self) -> None:
        """Membangun seluruh hierarki widget antarmuka."""
        # ── Header ──────────────────────────────────────────────
        header_frame = tk.Frame(self, bg=self.WARNA_HEADER_BG, height=56)
        header_frame.pack(fill=tk.X, side=tk.TOP)
        header_frame.pack_propagate(False)

        tk.Label(
            header_frame,
            text="🚚  Simulasi Sistem Logistik Transportasi Truk Nasional",
            font=(self.FONT_UI, 12, "bold"),
            bg=self.WARNA_HEADER_BG,
            fg=self.WARNA_HEADER_FG,
        ).pack(side=tk.LEFT, padx=16, pady=14)

        self.label_nomor_run = tk.Label(
            header_frame,
            text="Run: 0",
            font=(self.FONT_UI, 9),
            bg=self.WARNA_AKSEN,
            fg=self.WARNA_HEADER_FG,
            padx=10,
            pady=4,
            relief="flat",
        )
        self.label_nomor_run.pack(side=tk.RIGHT, padx=16, pady=14)

        # ── Notebook Tab ────────────────────────────────────────
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=6, pady=(6, 6))

        tab_pengaturan = ttk.Frame(self.notebook, padding=8)
        tab_output = ttk.Frame(self.notebook, padding=8)
        self.notebook.add(tab_pengaturan, text="  ⚙  Pengaturan & Kontrol  ")
        self.notebook.add(tab_output, text="  📋  Output & Log Simulasi  ")

        self._buat_tab_pengaturan(tab_pengaturan)
        self._buat_tab_output(tab_output)

        # Inisialisasi state awal dropdown
        self.perbarui_state_dropdown_od()
        self.perbarui_state_traffic_berdasarkan_routing()
        self.perbarui_state_traffic_checkbox()

    def _buat_tab_pengaturan(self, induk: ttk.Frame) -> None:
        """Membangun konten tab Pengaturan & Kontrol."""
        # ── Baris 1: Mode Perutean ──────────────────────────────
        kartu_routing = ttk.LabelFrame(
            induk, text="Mode Perutean & API", style="Kartu.TLabelframe", padding=10
        )
        kartu_routing.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(kartu_routing, text="Mode Perutean:").grid(
            row=0, column=0, padx=6, pady=4, sticky=tk.W
        )
        self.var_mode_perutean = tk.StringVar(self)
        opsi_routing = ["API Mapbox (Default)", "Model Rute Internal (Non-API)"]
        self.dropdown_mode_perutean = ttk.Combobox(
            kartu_routing,
            textvariable=self.var_mode_perutean,
            values=opsi_routing,
            width=30,
            state="readonly",
        )
        self.dropdown_mode_perutean.set(opsi_routing[0])
        self.dropdown_mode_perutean.grid(row=0, column=1, columnspan=2, padx=6, pady=4, sticky=tk.EW)
        self.dropdown_mode_perutean.bind(
            "<<ComboboxSelected>>", self.perbarui_state_traffic_berdasarkan_routing
        )

        self.var_hindari_lalu_lintas = tk.BooleanVar(value=True)
        self.checkbutton_traffic = ttk.Checkbutton(
            kartu_routing,
            text="Gunakan Data Lalu Lintas Real-time (API)",
            variable=self.var_hindari_lalu_lintas,
        )
        self.checkbutton_traffic.grid(row=0, column=3, columnspan=2, padx=6, pady=4, sticky=tk.W)

        for i in range(5):
            kartu_routing.columnconfigure(i, weight=1)

        # ── Baris 2: Parameter Armada & Waktu ───────────────────
        kartu_parameter = ttk.LabelFrame(
            induk, text="Parameter Simulasi", style="Kartu.TLabelframe", padding=10
        )
        kartu_parameter.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(kartu_parameter, text="Jumlah Truk:").grid(
            row=0, column=0, padx=6, pady=4, sticky=tk.W
        )
        self.entry_jumlah_truk = ttk.Entry(kartu_parameter, width=8)
        self.entry_jumlah_truk.insert(0, str(JUMLAH_TRUK_DEFAULT))
        self.entry_jumlah_truk.grid(row=0, column=1, padx=6, pady=4, sticky=tk.EW)

        ttk.Label(kartu_parameter, text="Jumlah Pengiriman:").grid(
            row=0, column=2, padx=6, pady=4, sticky=tk.W
        )
        self.entry_jumlah_pengiriman = ttk.Entry(kartu_parameter, width=8)
        self.entry_jumlah_pengiriman.insert(0, str(JUMLAH_PENGIRIMAN_DEFAULT))
        self.entry_jumlah_pengiriman.grid(row=0, column=3, padx=6, pady=4, sticky=tk.EW)

        ttk.Label(kartu_parameter, text="Durasi Permintaan (hari):").grid(
            row=0, column=4, padx=6, pady=4, sticky=tk.W
        )
        self.entry_durasi_simulasi = ttk.Entry(kartu_parameter, width=8)
        self.entry_durasi_simulasi.insert(0, "1")
        self.entry_durasi_simulasi.grid(row=0, column=5, padx=6, pady=4, sticky=tk.EW)

        for i in range(6):
            kartu_parameter.columnconfigure(i, weight=1)

        # ── Baris 3: Distribusi Pengiriman ──────────────────────
        kartu_distribusi = ttk.LabelFrame(
            induk, text="Distribusi Pengiriman & O-D", style="Kartu.TLabelframe", padding=10
        )
        kartu_distribusi.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(kartu_distribusi, text="Mode Distribusi:").grid(
            row=0, column=0, padx=6, pady=4, sticky=tk.W
        )
        self.var_mode_pengiriman = tk.StringVar(self)
        mode_distribusi = [
            "Acak ke Acak",
            "Satu Asal ke Satu Tujuan",
            "Satu Asal ke Banyak Tujuan (Acak)",
            "Banyak Asal (Acak) ke Satu Tujuan",
        ]
        self.dropdown_mode_pengiriman = ttk.Combobox(
            kartu_distribusi,
            textvariable=self.var_mode_pengiriman,
            values=mode_distribusi,
            width=30,
            state="readonly",
        )
        self.dropdown_mode_pengiriman.set(mode_distribusi[0])
        self.dropdown_mode_pengiriman.grid(
            row=0, column=1, columnspan=2, padx=6, pady=4, sticky=tk.EW
        )
        self.dropdown_mode_pengiriman.bind(
            "<<ComboboxSelected>>", self.perbarui_state_dropdown_od
        )

        ttk.Label(kartu_distribusi, text="Kota Asal Tetap:").grid(
            row=1, column=0, padx=6, pady=4, sticky=tk.W
        )
        self.var_kota_asal_tetap = tk.StringVar(self)
        self.dropdown_kota_asal = ttk.Combobox(
            kartu_distribusi,
            textvariable=self.var_kota_asal_tetap,
            values=DAFTAR_KOTA_DROPDOWN_ACAK,
            width=20,
            state="disabled",
        )
        self.dropdown_kota_asal.set(DAFTAR_KOTA_DROPDOWN_ACAK[0])
        self.dropdown_kota_asal.grid(row=1, column=1, padx=6, pady=4, sticky=tk.EW)

        ttk.Label(kartu_distribusi, text="Kota Tujuan Tetap:").grid(
            row=1, column=2, padx=6, pady=4, sticky=tk.W
        )
        self.var_kota_tujuan_tetap = tk.StringVar(self)
        self.dropdown_kota_tujuan = ttk.Combobox(
            kartu_distribusi,
            textvariable=self.var_kota_tujuan_tetap,
            values=DAFTAR_KOTA_DROPDOWN_ACAK,
            width=20,
            state="disabled",
        )
        self.dropdown_kota_tujuan.set(DAFTAR_KOTA_DROPDOWN_ACAK[0])
        self.dropdown_kota_tujuan.grid(row=1, column=3, padx=6, pady=4, sticky=tk.EW)

        for i in range(5):
            kartu_distribusi.columnconfigure(i, weight=1)

        # ── Baris 4: Skenario & Depot ────────────────────────────
        kartu_skenario = ttk.LabelFrame(
            induk, text="Skenario & Konfigurasi Depot", style="Kartu.TLabelframe", padding=10
        )
        kartu_skenario.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(kartu_skenario, text="Skenario Studi Kasus:").grid(
            row=0, column=0, padx=6, pady=4, sticky=tk.W
        )
        self.var_skenario = tk.StringVar(self)
        daftar_skenario = [
            "Simulasi Umum",
            "Skenario 1 (Rute Tetap & Statis)",
            "Skenario 2 (Rute Dinamis & Inter-Truck)",
            "Skenario 3 (Pengiriman Gabungan/Konsolidasi)",
        ]
        self.dropdown_skenario = ttk.Combobox(
            kartu_skenario,
            textvariable=self.var_skenario,
            values=daftar_skenario,
            width=38,
            state="readonly",
        )
        self.dropdown_skenario.set(daftar_skenario[0])
        self.dropdown_skenario.grid(
            row=0, column=1, columnspan=3, padx=6, pady=4, sticky=tk.EW
        )
        self.dropdown_skenario.bind(
            "<<ComboboxSelected>>", self.perbarui_state_traffic_checkbox
        )

        ttk.Label(kartu_skenario, text="Kota Depot (pisah koma):").grid(
            row=1, column=0, padx=6, pady=4, sticky=tk.W
        )
        self.entry_kota_depot = ttk.Entry(kartu_skenario, width=50)
        self.entry_kota_depot.grid(
            row=1, column=1, columnspan=4, padx=6, pady=4, sticky=tk.EW
        )
        ttk.Label(
            kartu_skenario,
            text="Contoh: Jakarta,Medan,Surabaya",
            foreground="#757575",
            font=(self.FONT_UI, 8),
        ).grid(row=2, column=1, columnspan=4, padx=6, sticky=tk.W)

        for i in range(5):
            kartu_skenario.columnconfigure(i, weight=1)

        # ── Tombol Mulai ─────────────────────────────────────────
        frame_tombol = ttk.Frame(induk)
        frame_tombol.pack(fill=tk.X, pady=(4, 4))

        self.tombol_mulai = ttk.Button(
            frame_tombol,
            text="▶  Mulai Simulasi",
            command=self.mulai_thread_simulasi,
            style="Aksen.TButton",
        )
        self.tombol_mulai.pack(fill=tk.X, ipady=4)

        # ── Status Bar ───────────────────────────────────────────
        self.label_status = tk.Label(
            induk,
            text="Siap — Atur parameter di atas lalu tekan Mulai Simulasi.",
            anchor=tk.W,
            fg="#546e7a",
            bg=self.WARNA_LATAR,
            font=(self.FONT_UI, 9),
            padx=4,
        )
        self.label_status.pack(fill=tk.X, pady=(4, 0))

    def _buat_tab_output(self, induk: ttk.Frame) -> None:
        """Membangun konten tab Output & Log Simulasi."""
        # Header tab output
        frame_header_output = tk.Frame(induk, bg=self.WARNA_PANEL)
        frame_header_output.pack(fill=tk.X, pady=(0, 6))

        tk.Label(
            frame_header_output,
            text="Log & Hasil Simulasi",
            font=(self.FONT_UI, 11, "bold"),
            fg=self.WARNA_AKSEN,
            bg=self.WARNA_PANEL,
        ).pack(side=tk.LEFT)

        self.tombol_bersihkan = ttk.Button(
            frame_header_output,
            text="🗑 Bersihkan",
            command=lambda: self.area_output.delete("1.0", tk.END),
            width=12,
        )
        self.tombol_bersihkan.pack(side=tk.RIGHT)

        # Area teks output
        frame_output = ttk.Frame(induk)
        frame_output.pack(fill=tk.BOTH, expand=True)

        self.area_output = tk.Text(
            frame_output,
            wrap=tk.WORD,
            font=self.font_log,
            bg="#1e1e1e",
            fg="#d4d4d4",
            insertbackground="#ffffff",
            selectbackground="#264f78",
            padx=12,
            pady=10,
            relief="flat",
            borderwidth=0,
            state=tk.NORMAL,
        )

        # Tag warna untuk output
        self.area_output.tag_configure("header",   foreground="#4fc3f7", font=(self.FONT_MONO, 10, "bold"))
        self.area_output.tag_configure("sukses",   foreground="#81c784")
        self.area_output.tag_configure("peringatan", foreground="#ffb74d")
        self.area_output.tag_configure("bahaya",   foreground="#e57373")
        self.area_output.tag_configure("info",     foreground="#b0bec5")
        self.area_output.tag_configure("label",    foreground="#80cbc4")

        scrollbar_output = ttk.Scrollbar(frame_output, command=self.area_output.yview)
        self.area_output.config(yscrollcommand=scrollbar_output.set)
        scrollbar_output.pack(side=tk.RIGHT, fill=tk.Y)
        self.area_output.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

    # ─────────────────────────────────────────────────────────────
    # 7.2 KONTROL STATE ANTARMUKA
    # ─────────────────────────────────────────────────────────────

    def perbarui_state_dropdown_od(self, event=None) -> None:
        """Mengatur enabled/disabled dropdown Asal/Tujuan berdasarkan mode distribusi."""
        mode = self.var_mode_pengiriman.get()

        if mode == "Satu Asal ke Satu Tujuan":
            self.dropdown_kota_asal.config(state="readonly")
            self.dropdown_kota_tujuan.config(state="readonly")

        elif mode == "Satu Asal ke Banyak Tujuan (Acak)":
            self.dropdown_kota_asal.config(state="readonly")
            self.dropdown_kota_tujuan.config(state="disabled")
            self.var_kota_tujuan_tetap.set(DAFTAR_KOTA_DROPDOWN_ACAK[0])

        elif mode == "Banyak Asal (Acak) ke Satu Tujuan":
            self.dropdown_kota_asal.config(state="disabled")
            self.dropdown_kota_tujuan.config(state="readonly")
            self.var_kota_asal_tetap.set(DAFTAR_KOTA_DROPDOWN_ACAK[0])

        else:  # Acak ke Acak
            self.dropdown_kota_asal.config(state="disabled")
            self.dropdown_kota_tujuan.config(state="disabled")
            self.var_kota_asal_tetap.set(DAFTAR_KOTA_DROPDOWN_ACAK[0])
            self.var_kota_tujuan_tetap.set(DAFTAR_KOTA_DROPDOWN_ACAK[0])

    def perbarui_state_traffic_berdasarkan_routing(self, event=None) -> None:
        """Mengatur state checkbutton traffic berdasarkan mode perutean."""
        mode_routing = self.var_mode_perutean.get()

        if mode_routing == "Model Rute Internal (Non-API)":
            self.var_hindari_lalu_lintas.set(False)
            self.checkbutton_traffic.config(state="disabled")
            self.dropdown_skenario.config(state="disabled")
            self.var_skenario.set("Simulasi Umum")
        else:
            self.checkbutton_traffic.config(state="normal")
            self.dropdown_skenario.config(state="readonly")
            self.perbarui_state_traffic_checkbox()

    def perbarui_state_traffic_checkbox(self, event=None) -> None:
        """
        Mengunci/mengizinkan checkbutton traffic berdasarkan skenario yang dipilih,
        sesuai spesifikasi: Skenario 1 tidak pakai traffic, Skenario 2 wajib pakai.
        """
        skenario = self.var_skenario.get()
        mode_routing = self.var_mode_perutean.get()

        if mode_routing == "API Mapbox (Default)":
            self.checkbutton_traffic.config(state="normal")
            if "Skenario 1" in skenario:
                self.var_hindari_lalu_lintas.set(False)
                self.checkbutton_traffic.config(state="disabled")
            elif "Skenario 2" in skenario:
                self.var_hindari_lalu_lintas.set(True)
                self.checkbutton_traffic.config(state="disabled")
        else:
            self.var_hindari_lalu_lintas.set(False)
            self.checkbutton_traffic.config(state="disabled")

    # ─────────────────────────────────────────────────────────────
    # 7.3 EKSEKUSI SIMULASI (Threading)
    # ─────────────────────────────────────────────────────────────

    def mulai_thread_simulasi(self) -> None:
        """Memulai thread simulasi dan menonaktifkan tombol mulai."""
        self.tombol_mulai.config(state="disabled", text="⏳  Simulasi sedang berjalan...")
        self.label_status.config(text="Simulasi sedang berjalan — mohon tunggu...")
        self.area_output.delete("1.0", tk.END)
        self._tulis_log("=" * 78, "header")
        self._tulis_log("  SIMULASI DIMULAI — Mempersiapkan sistem...\n", "header")
        self.notebook.select(1)  # Pindah ke tab output

        thread = threading.Thread(target=self.pekerja_simulasi, daemon=True)
        thread.start()

    def pekerja_simulasi(self) -> None:
        """Menjalankan logika simulasi di thread terpisah (mencegah GUI freeze)."""
        try:
            jumlah_truk = int(self.entry_jumlah_truk.get())
            jumlah_pengiriman = int(self.entry_jumlah_pengiriman.get())
            durasi_simulasi = int(self.entry_durasi_simulasi.get())

            if jumlah_truk <= 0 or jumlah_pengiriman <= 0 or durasi_simulasi <= 0:
                raise ValueError("Jumlah truk, pengiriman, dan durasi harus lebih dari 0.")

            mode_perutean = self.var_mode_perutean.get()
            mode_distribusi = self.var_mode_pengiriman.get()

            # Validasi kota asal/tujuan
            nilai_asal = self.var_kota_asal_tetap.get()
            kota_asal_terpilih = (
                nilai_asal
                if nilai_asal != DAFTAR_KOTA_DROPDOWN_ACAK[0]
                and self.dropdown_kota_asal["state"] != "disabled"
                else None
            )
            nilai_tujuan = self.var_kota_tujuan_tetap.get()
            kota_tujuan_terpilih = (
                nilai_tujuan
                if nilai_tujuan != DAFTAR_KOTA_DROPDOWN_ACAK[0]
                and self.dropdown_kota_tujuan["state"] != "disabled"
                else None
            )

            if mode_distribusi == "Satu Asal ke Satu Tujuan":
                if (
                    not kota_asal_terpilih
                    or not kota_tujuan_terpilih
                    or kota_asal_terpilih == kota_tujuan_terpilih
                ):
                    raise ValueError(
                        "Mode 'Satu Asal ke Satu Tujuan' memerlukan kota asal dan tujuan "
                        "yang valid dan berbeda."
                    )
            if mode_distribusi == "Satu Asal ke Banyak Tujuan (Acak)" and not kota_asal_terpilih:
                raise ValueError("Mode ini memerlukan Kota Asal Tetap yang valid.")
            if mode_distribusi == "Banyak Asal (Acak) ke Satu Tujuan" and not kota_tujuan_terpilih:
                raise ValueError("Mode ini memerlukan Kota Tujuan Tetap yang valid.")

            self.nomor_run_simulasi += 1
            skenario_dipilih = self.var_skenario.get()
            hindari_lalu_lintas = self.var_hindari_lalu_lintas.get()
            string_kota_depot = self.entry_kota_depot.get()

            # Jalankan simulasi melalui MesinSimulasi
            mesin = MesinSimulasi()
            (
                hasil_trip,
                pengiriman_diproses,
                armada_truk,
                path_peta_statis,
                path_peta_dinamis,
            ) = mesin.jalankan_simulasi(
                jumlah_truk=jumlah_truk,
                jumlah_pengiriman=jumlah_pengiriman,
                durasi_simulasi_hari=durasi_simulasi,
                hindari_lalu_lintas=hindari_lalu_lintas,
                nomor_run=self.nomor_run_simulasi,
                mode_perutean=mode_perutean,
                mode_distribusi=mode_distribusi,
                skenario_dipilih=skenario_dipilih,
                kota_asal_tetap=kota_asal_terpilih,
                kota_tujuan_tetap=kota_tujuan_terpilih,
                string_kota_depot=string_kota_depot if string_kota_depot else None,
            )

            # Jadwalkan callback ke main thread
            self.after(
                0,
                self.simulasi_selesai,
                hasil_trip,
                pengiriman_diproses,
                armada_truk,
                path_peta_statis,
                path_peta_dinamis,
                skenario_dipilih,
            )

        except Exception as err:  # pylint: disable=broad-except
            self.after(0, self.simulasi_error, err)

    # ─────────────────────────────────────────────────────────────
    # 7.4 CALLBACK HASIL SIMULASI
    # ─────────────────────────────────────────────────────────────

    def simulasi_selesai(
        self,
        hasil_trip: List[Dict],
        pengiriman_diproses: List[Pengiriman],
        armada_truk: List[Truk],
        path_peta_statis: Optional[str],
        path_peta_dinamis: Optional[str],
        nama_skenario: str,
    ) -> None:
        """Dipanggil di main thread setelah simulasi selesai — menampilkan hasil."""
        self.label_nomor_run.config(text=f"Run: {self.nomor_run_simulasi}")

        self._tulis_log("=" * 78 + "\n", "header")
        self._tulis_log(
            f"  HASIL AKHIR — {nama_skenario} (Run {self.nomor_run_simulasi})\n",
            "header",
        )
        self._tulis_log("=" * 78 + "\n\n", "header")

        # Formula Biaya
        self._tulis_log("── Formula Biaya Operasional ─────────────────────────────\n", "label")
        self._tulis_log(f"  Tarif BBM per Liter          : Rp{TARIF_BBM:>12,.0f}\n", "info")
        self._tulis_log(f"  Gaji Sopir per Jam           : Rp{GAJI_SOPIR_PER_JAM:>12,.0f}\n", "info")
        self._tulis_log(f"  Biaya Pemeliharaan per Trip  : Rp{BIAYA_PEMELIHARAAN_PER_TRIP:>12,.0f}\n", "info")
        self._tulis_log(
            f"  Konsumsi BBM (Stokastik)     : "
            f"{MIN_KONSUMSI_BBM_LITER_PER_JAM}–{MAKS_KONSUMSI_BBM_LITER_PER_JAM} Liter/Jam\n",
            "info",
        )
        self._tulis_log(
            "  Fungsi Biaya Perjalanan      : "
            "(Waktu × Gaji Sopir) + (Waktu × Konsumsi BBM × Tarif BBM)\n",
            "info",
        )
        self._tulis_log(
            "  Fungsi Biaya Total Trip      : Biaya Perjalanan + Biaya Pemeliharaan\n\n",
            "info",
        )

        # Detail per pengiriman
        self._tulis_log("── Detail per Pengiriman ─────────────────────────────────\n", "label")
        pengiriman_berhasil = [
            p for p in pengiriman_diproses if p.status_pengiriman.startswith("selesai")
        ]
        if not pengiriman_berhasil:
            self._tulis_log("  Tidak ada pengiriman yang berhasil diselesaikan.\n\n", "peringatan")
        else:
            for p in pengiriman_berhasil:
                self._tulis_detail_pengiriman(p)

        # Detail per truk
        self._tulis_log("── Detail per Armada ─────────────────────────────────────\n", "label")
        armada_beroperasi = [t for t in armada_truk if t.jumlah_trip_selesai > 0]
        if not armada_beroperasi:
            self._tulis_log("  Tidak ada truk yang beroperasi.\n\n", "peringatan")
        else:
            for t in armada_beroperasi:
                self._tulis_detail_truk(t)

        # Kinerja keseluruhan
        self._tulis_log("── Kinerja Keseluruhan ───────────────────────────────────\n", "label")
        self._tulis_kinerja_keseluruhan(pengiriman_diproses, armada_truk)

        # Buka peta di browser
        self.update_idletasks()
        self._buka_peta_dengan_aman(path_peta_statis, "statis")
        self._buka_peta_dengan_aman(path_peta_dinamis, "animasi")

        # Notifikasi & reset tombol
        self.label_status.config(
            text=f"Simulasi Run {self.nomor_run_simulasi} selesai. "
                 f"File peta disimpan di: {DIREKTORI_SIMPAN}"
        )
        messagebox.showinfo(
            "Simulasi Selesai",
            f"{nama_skenario} (Run {self.nomor_run_simulasi}) berhasil diselesaikan.\n\n"
            f"File peta disimpan di:\n{DIREKTORI_SIMPAN}",
        )
        self.tombol_mulai.config(state="normal", text="▶  Mulai Simulasi")

    def _tulis_detail_pengiriman(self, p: Pengiriman) -> None:
        """Menulis blok detail satu pengiriman ke area output."""
        waktu_tunggu_menit = (
            (p.waktu_truk_dialokasikan - p.waktu_permintaan_dibuat) / 60
            if p.waktu_truk_dialokasikan > 0
            else 0.0
        )

        jarak_ke_muat_km = 0.0
        waktu_ke_muat_menit = 0.0
        if p.rute_depot_ke_asal_json and "summary" in p.rute_depot_ke_asal_json:
            jarak_ke_muat_km = p.rute_depot_ke_asal_json["summary"]["lengthInMeters"] / 1000
            waktu_ke_muat_menit = (
                p.rute_depot_ke_asal_json["summary"]["travelTimeInSeconds"] / 60
            )

        if p.waktu_penyelesaian_aktual > 0 and p.waktu_permintaan_dibuat >= 0:
            total_siklus_menit = (
                (p.waktu_penyelesaian_aktual - p.waktu_permintaan_dibuat) / 60
            )
        else:
            total_siklus_menit = 0.0

        tag_sla = "sukses" if p.status_pengiriman == "selesai" else "peringatan"
        teks_sla = "✔ Tepat Waktu" if p.status_pengiriman == "selesai" else "✖ Terlambat"

        self._tulis_log(
            f"  [{p.id_pengiriman}] Truk: {p.id_truk_ditugaskan} | "
            f"{p.kota_asal} → {p.kota_tujuan} | "
            f"{p.jumlah_barang_ton:.1f} Ton\n",
            "info",
        )

        if hasattr(p, 'info_is_backhaul'):
            if p.info_is_backhaul:
                self._tulis_log(
                    f"  {'':4}Optimasi      : !!! BACKHAUL DETECTED !!!\n"
                    f"  {'':4}Kendaraan     : {p.info_jenis_truk} (Rp{p.info_tarif_truk:,.0f}/km)\n",
                    "sukses"
                )
            else:
                self._tulis_log(
                    f"  {'':4}Optimasi      : Standar\n"
                    f"  {'':4}Kendaraan     : {p.info_jenis_truk} (Rp{p.info_tarif_truk:,.0f}/km)\n",
                    "info"
                )
                
        self._tulis_log(
            f"  {'':4}Jarak Utama   : {p.jarak_tempuh_km:>8.2f} km  |  "
            f"Biaya: Rp{p.biaya_pengiriman_total:>12,.0f}\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Waktu Tunggu  : {waktu_tunggu_menit:>8.1f} menit\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Ke Lok. Muat  : {waktu_ke_muat_menit:>8.1f} menit "
            f"({jarak_ke_muat_km:.2f} km)\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Proses Muat   : {p.estimasi_waktu_muat_menit:>8.1f} menit\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Waktu Tempuh  : {p.estimasi_waktu_tempuh_menit:>8.1f} menit\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Proses Bongkar: {p.estimasi_waktu_bongkar_menit:>8.1f} menit\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}{'─' * 50}\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Total Siklus  : {total_siklus_menit:>8.1f} menit "
            f"({total_siklus_menit / 60:.2f} jam)\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Target SLA    : {p.target_sla_menit:>8.1f} menit | "
            f"Status SLA: ",
            "info",
        )
        self._tulis_log(f"{teks_sla}\n\n", tag_sla)

    def _tulis_detail_truk(self, t: Truk) -> None:
        """Menulis blok detail satu truk ke area output."""
        total_biaya = t.total_biaya_bbm + t.total_biaya_sopir + t.total_biaya_pemeliharaan
        self._tulis_log(
            f"  [{t.id_truk}] Depot: {t.lokasi_depot} | "
            f"Trip Selesai: {t.jumlah_trip_selesai}\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Total Jarak    : {t.total_km_operasional:>10.2f} km\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Total Mengemudi: {t.total_jam_mengemudi:>10.2f} jam\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Biaya BBM      : Rp{t.total_biaya_bbm:>12,.0f}\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Biaya Sopir    : Rp{t.total_biaya_sopir:>12,.0f}\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Pemeliharaan   : Rp{t.total_biaya_pemeliharaan:>12,.0f}\n",
            "info",
        )
        self._tulis_log(
            f"  {'':4}Total Biaya    : Rp{total_biaya:>12,.0f}\n\n",
            "sukses",
        )

    def _tulis_kinerja_keseluruhan(
        self, pengiriman_diproses: List[Pengiriman], armada_truk: List[Truk]
    ) -> None:
        """Menulis blok ringkasan kinerja keseluruhan ke area output."""
        tepat_waktu = sum(
            1 for p in pengiriman_diproses if p.status_pengiriman == "selesai"
        )
        terlambat = sum(
            1 for p in pengiriman_diproses if p.status_pengiriman == "selesai_terlambat"
        )
        gagal = len(pengiriman_diproses) - tepat_waktu - terlambat
        total = len(pengiriman_diproses)
        total_biaya = sum(
            t.total_biaya_bbm + t.total_biaya_sopir + t.total_biaya_pemeliharaan
            for t in armada_truk
        )
        persen_tepat = (tepat_waktu / total * 100) if total > 0 else 0.0

        self._tulis_log(f"  Tepat Waktu   : {tepat_waktu:>3} / {total}\n", "sukses")
        self._tulis_log(f"  Terlambat     : {terlambat:>3} / {total}\n", "peringatan")
        self._tulis_log(f"  Gagal/Tidak Terproses: {gagal:>3} / {total}\n", "bahaya")
        self._tulis_log(f"  Tingkat Keberhasilan  : {persen_tepat:.1f}%\n", "info")
        self._tulis_log(
            f"  Total Biaya Operasional: Rp{total_biaya:>14,.0f}\n\n",
            "sukses",
        )

    def simulasi_error(self, error: Exception) -> None:
        """Dipanggil di main thread jika terjadi error saat eksekusi simulasi."""
        self._tulis_log(f"\n\n{'!' * 60}\n", "bahaya")
        self._tulis_log(f"  ERROR SIMULASI: {error}\n", "bahaya")
        self._tulis_log(f"{'!' * 60}\n\n", "bahaya")
        self._tulis_log(traceback.format_exc(), "bahaya")

        self.label_status.config(text=f"Error: {error}")
        messagebox.showerror(
            "Error Simulasi",
            f"Terjadi kesalahan saat menjalankan simulasi:\n\n{error}",
        )
        self.tombol_mulai.config(state="normal", text="▶  Mulai Simulasi")

    # ─────────────────────────────────────────────────────────────
    # 7.5 HELPER OUTPUT
    # ─────────────────────────────────────────────────────────────

    def _tulis_log(self, teks: str, tag: str = "info") -> None:
        """Menulis teks ke area output dengan tag warna yang sesuai."""
        self.area_output.insert(tk.END, teks, tag)
        self.area_output.see(tk.END)

    def _buka_peta_dengan_aman(
        self, path_peta: Optional[str], jenis_peta: str
    ) -> bool:
        """Membuka file peta di browser — menampilkan pesan log jika gagal."""
        if path_peta and os.path.exists(path_peta):
            pesan = f"Peta {jenis_peta} disimpan di:\n  {path_peta}\n"
            self._tulis_log(pesan, "sukses")
            try:
                webbrowser.open(f"file:///{os.path.realpath(path_peta)}")
            except Exception:  # pylint: disable=broad-except
                print(f"Gagal membuka browser: {traceback.format_exc()}")
            return True

        pesan_error = f"File peta {jenis_peta} tidak ditemukan atau gagal dibuat.\n"
        self._tulis_log(pesan_error, "peringatan")
        return False


# =============================================================================
# BAGIAN 8 — TITIK MASUK PROGRAM
# =============================================================================

if __name__ == "__main__":
    aplikasi = SimulasiApp()
    aplikasi.mainloop()