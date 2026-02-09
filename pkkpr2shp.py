# full_streamlit_pkkpr.py (optimized)
import streamlit as st
import geopandas as gpd
import pandas as pd
import io, os, zipfile, tempfile, re, math
from shapely.geometry import Point, Polygon, MultiPolygon, GeometryCollection, MultiPoint, LineString
from shapely.validation import make_valid
from shapely.ops import unary_union, polygonize_full
import folium
from streamlit_folium import st_folium
import pdfplumber
import matplotlib.pyplot as plt
import contextily as ctx
from folium.plugins import Fullscreen
import xyzservices.providers as xyz
from pyproj import Transformer
from math import atan2
import matplotlib.patches as mpatches
import matplotlib.lines as mlines

# ======================
# CONFIG
# ======================
st.set_page_config(
    page_title="PKKPR → SHP + Overlay (Final)", 
    layout="wide",
    initial_sidebar_state="expanded"
)
st.title("PKKPR → Shapefile Converter & Overlay Tapak Proyek (Final)")
st.markdown("---")

# Inisialisasi session state
if 'gdf_polygon' not in st.session_state:
    st.session_state.gdf_polygon = None
if 'gdf_points' not in st.session_state:
    st.session_state.gdf_points = None
if 'gdf_tapak' not in st.session_state:
    st.session_state.gdf_tapak = None
if 'luas_pkkpr_doc' not in st.session_state:
    st.session_state.luas_pkkpr_doc = None
if 'uploaded_file_name' not in st.session_state:
    st.session_state.uploaded_file_name = None
if 'uploaded_tapak_name' not in st.session_state:
    st.session_state.uploaded_tapak_name = None

DEBUG = st.sidebar.checkbox("Tampilkan debug logs", value=False)
INDO_BOUNDS = (95.0, 141.0, -11.0, 6.0)

# ======================
# HELPERS dengan CACHING
# ======================
@st.cache_data(ttl=3600)
def format_angka_id(value):
    try:
        val = float(value)
        if abs(val - round(val)) < 0.001:
            return f"{int(round(val)):,}".replace(",", ".")
        else:
            s = f"{val:,.2f}"
            s = s.replace(",", "X").replace(".", ",").replace("X", ".")
            return s
    except:
        return str(value)

@st.cache_data(ttl=3600)
def get_utm_info(lon, lat):
    zone = int((lon + 180) / 6) + 1
    epsg = 32600 + zone if lat >= 0 else 32700 + zone
    zone_label = f"{zone}{'N' if lat >= 0 else 'S'}"
    return epsg, zone_label

@st.cache_data(ttl=3600)
def parse_luas_line(line):
    if not line:
        return None
    s = str(line).replace('\xa0', ' ').replace('\u00B2', '²').strip()
    s_norm = re.sub(r"\s+", " ", s).upper()
    m = re.search(r"([0-9]+(?:[.,][0-9]+)*)\s*(M2|M²|HA|HEKTAR)\b", s_norm)
    if m:
        num_raw, unit_raw = m.group(1), m.group(2).upper()
        unit_out = "Ha" if "HA" in unit_raw else "m²"
        return f"{num_raw} {unit_out}"
    m2 = re.search(r"([0-9]+(?:[.,][0-9]+)*)\b", s)
    if m2:
        return m2.group(1)
    return None

@st.cache_data(ttl=3600)
def save_shapefile_layers(gdf_poly, gdf_points):
    with tempfile.TemporaryDirectory() as tmpdir:
        if gdf_poly is not None and not gdf_poly.empty:
            gdf_poly.to_crs(epsg=4326).to_file(os.path.join(tmpdir, "PKKPR_Polygon.shp"))
        if gdf_points is not None and not gdf_points.empty:
            gdf_points.to_crs(epsg=4326).to_file(os.path.join(tmpdir, "PKKPR_Points.shp"))
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
            for f in os.listdir(tmpdir):
                zf.write(os.path.join(tmpdir, f), arcname=f)
        buf.seek(0)
        return buf.read()

@st.cache_data(ttl=3600)
def fix_geometry(gdf):
    if gdf is None or gdf.empty:
        return gdf
    gdf["geometry"] = gdf["geometry"].apply(make_valid)
    def extract_valid(geom):
        if geom is None:
            return None
        if geom.geom_type == "GeometryCollection":
            polys = [g for g in geom.geoms if g.geom_type in ["Polygon", "MultiPolygon"]]
            return polys[0] if len(polys) == 1 else MultiPolygon(polys) if polys else None
        return geom
    gdf["geometry"] = gdf["geometry"].apply(extract_valid)
    return gdf

@st.cache_data(ttl=3600)
def try_parse_float(s):
    try:
        return float(str(s).strip().replace(",", "."))
    except:
        return None

@st.cache_data(ttl=3600)
def dms_to_decimal(dms_str):
    if not dms_str or not isinstance(dms_str, str):
        return None
    s = dms_str.strip().upper()
    s = (
        s.replace(",", ".")
         .replace("º", "°")
         .replace("’", "'")
         .replace("‘", "'")
         .replace("″", '"')
         .replace("”", '"')
         .replace("“", '"')
         .replace("  ", " ")
    )
    s = s.replace("BT", "E").replace("BB", "W").replace("LS", "S").replace("LU", "N")
    direction_match = re.search(r"\b([NSEW])\b", s)
    direction = direction_match.group(1) if direction_match else None
    s = re.sub(r"[NSEW]", "", s).strip()
    dms_pattern = re.findall(r"[-+]?\d+(?:\.\d+)?", s)
    if not dms_pattern:
        return None
    try:
        deg = float(dms_pattern[0])
        minutes = float(dms_pattern[1]) if len(dms_pattern) > 1 else 0.0
        seconds = float(dms_pattern[2]) if len(dms_pattern) > 2 else 0.0
    except Exception:
        return None
    val = deg + (minutes / 60.0) + (seconds / 3600.0)
    if direction in ["S", "W"]:
        val *= -1
    if not (-180 <= val <= 180):
        return None
    return val

# ======================
# TAMPILKAN TABEL DATA SHP
# ======================
def display_shapefile_table(gdf, title):
    if gdf is None or gdf.empty:
        return
    
    with st.container():
        st.write(f"**Tabel Data {title}**")
        st.caption(f"{len(gdf)} fitur, {len(gdf.columns)} kolom")
        
        display_df = gdf.copy()
        if 'geometry' in display_df.columns:
            def format_geometry(geom):
                if geom is None:
                    return None
                geom_type = geom.geom_type
                if geom_type == 'Point':
                    return f"Point ({geom.x:.6f}, {geom.y:.6f})"
                elif geom_type == 'LineString':
                    return f"LineString ({len(geom.coords)} titik)"
                elif geom_type == 'Polygon':
                    return f"Polygon ({len(geom.exterior.coords)} titik exterior)"
                elif geom_type == 'MultiPolygon':
                    total_points = sum(len(poly.exterior.coords) for poly in geom.geoms)
                    return f"MultiPolygon ({len(geom.geoms)} polygon, {total_points} titik)"
                else:
                    return geom_type
            display_df['geometry'] = display_df['geometry'].apply(format_geometry)
        
        st.dataframe(display_df, use_container_width=True, height=300)
        
        csv = display_df.to_csv(index=False).encode('utf-8')
        st.download_button(
            label=f"📥 Download CSV {title}",
            data=csv,
            file_name=f"{title.replace(' ', '_')}_data.csv",
            mime="text/csv",
            key=f"csv_{title}_{hash(str(gdf.geometry.iloc[0])) if not gdf.empty else 'empty'}"
        )

# ======================
# UNIVERSAL PDF PARSER dengan CACHING
# ======================
@st.cache_data(ttl=3600, show_spinner=False)
def extract_tables_and_coords_from_pdf(uploaded_file):
    coords_plain = []
    text_all = ""
    ordered_from_table = False

    with pdfplumber.open(uploaded_file) as pdf:
        for page in pdf.pages:
            text_all += (page.extract_text() or "") + "\n"

    coords_with_no = []
    with pdfplumber.open(uploaded_file) as pdf:
        for page in pdf.pages:
            table = page.extract_table()
            if not table:
                continue
            try:
                df = pd.DataFrame(table[1:], columns=table[0])
            except:
                df = pd.DataFrame(table)
            df.columns = [re.sub(r"\s+", " ", str(c)).strip().lower() for c in df.columns]
            no_col, bujur_col, lintang_col = None, None, None
            for col in df.columns:
                if re.match(r"no\b", col):
                    no_col = col
                if any(k in col for k in ["bujur", "longitude", "long", "x"]):
                    bujur_col = col
                if any(k in col for k in ["lintang", "latitude", "lat", "y"]):
                    lintang_col = col

            if bujur_col and lintang_col:
                for _, row in df.iterrows():
                    raw_no = row.get(no_col, None)
                    raw_bujur = str(row.get(bujur_col, "")).strip()
                    raw_lintang = str(row.get(lintang_col, "")).strip()

                    def looks_like_dms(s):
                        return any(sym in s.upper() for sym in ["°", "º", "'", "’", '"', "BT", "LS", "LU", "E", "W"]) 

                    lon = dms_to_decimal(raw_bujur) if looks_like_dms(raw_bujur) else try_parse_float(raw_bujur)
                    lat = dms_to_decimal(raw_lintang) if looks_like_dms(raw_lintang) else try_parse_float(raw_lintang)

                    if lon and lat:
                        if not (95 <= lon <= 141 and -11 <= lat <= 6) and (95 <= lat <= 141 and -11 <= lon <= 6):
                            lon, lat = lat, lon
                        if 95 <= lon <= 141 and -11 <= lat <= 6:
                            try:
                                n = int(str(raw_no).strip()) if raw_no not in [None, ""] else None
                            except:
                                n = None
                            coords_with_no.append((n, lon, lat))

    if coords_with_no:
        coords_with_no.sort(key=lambda x: (x[0] if x[0] is not None else 99999))
        coords_plain = [(lon, lat) for _, lon, lat in coords_with_no]
        ordered_from_table = True

    if not coords_plain:
        num_pattern = re.compile(r"-?\d{1,3}(?:[.,]\d+)+")
        for line in text_all.splitlines():
            nums = num_pattern.findall(line)
            if len(nums) >= 2:
                a, b = try_parse_float(nums[0]), try_parse_float(nums[1])
                if a and b:
                    if 95 <= a <= 141 and -11 <= b <= 6:
                        coords_plain.append((a, b))
                    elif 95 <= b <= 141 and -11 <= a <= 6:
                        coords_plain.append((b, a))

    seen, unique_coords = set(), []
    for xy in coords_plain:
        key = (round(xy[0], 6), round(xy[1], 6))
        if key not in seen:
            unique_coords.append(xy)
            seen.add(key)

    return {"coords": unique_coords, "luas": None, "ordered": ordered_from_table}

# ======================
# AUTO SORT KOORDINAT
# ======================
@st.cache_data(ttl=3600)
def sort_coords_clockwise(coords):
    if not coords:
        return coords
    cx = sum(x for x, y in coords) / len(coords)
    cy = sum(y for x, y in coords) / len(coords)
    coords_sorted = sorted(coords, key=lambda p: math.atan2(p[1]-cy, p[0]-cx))
    return coords_sorted

# ======================
# FUNGSI PROCESSING UTAMA
# ======================
def process_pkkpr_file(uploaded):
    """Process PKKPR file dan simpan ke session state"""
    if uploaded.name.lower().endswith(".pdf"):
        parsed = extract_tables_and_coords_from_pdf(uploaded)
        coords = parsed["coords"]
        st.session_state.luas_pkkpr_doc = parsed["luas"]
        ordered_flag = parsed.get("ordered", False)
        
        if coords:
            pts = [Point(x, y) for x, y in coords]
            st.session_state.gdf_points = gpd.GeoDataFrame(geometry=pts, crs="EPSG:4326")
            
            coords_proc = coords.copy()
            if not ordered_flag:
                coords_proc = sort_coords_clockwise(coords_proc)
            
            if coords_proc[0] != coords_proc[-1]:
                coords_proc.append(coords_proc[0])
            
            poly_candidate = None
            tried = []
            
            try:
                poly_candidate = Polygon(coords_proc)
                tried.append("Polygon(raw coords)")
                
                if not getattr(poly_candidate, "is_valid", False) or getattr(poly_candidate, "area", 0) == 0:
                    try:
                        poly_candidate = poly_candidate.buffer(0)
                        tried.append("buffer(0)")
                    except Exception:
                        pass
                
                if (not getattr(poly_candidate, "is_valid", False)) or getattr(poly_candidate, "area", 0) == 0:
                    try:
                        ls = LineString(coords_proc)
                        polys, dangles, cuts, invalids = polygonize_full(ls)
                        if polys:
                            try:
                                poly_list = list(polys)
                            except Exception:
                                poly_list = polys
                            if poly_list:
                                poly_candidate = max(poly_list, key=lambda p: p.area)
                                tried.append("polygonize_full")
                    except Exception:
                        pass
                
                if (poly_candidate is None) or (not getattr(poly_candidate, "is_valid", False)) or getattr(poly_candidate, "area", 0) == 0:
                    mp = MultiPoint(coords_proc)
                    ch = mp.convex_hull
                    if ch.geom_type == "Polygon" and ch.area > 0:
                        poly_candidate = ch
                        tried.append("convex_hull")
            except Exception:
                poly_candidate = None
            
            if poly_candidate is not None and getattr(poly_candidate, "is_valid", False) and getattr(poly_candidate, "area", 0) > 0:
                st.session_state.gdf_polygon = gpd.GeoDataFrame(geometry=[poly_candidate], crs="EPSG:4326")
                st.session_state.gdf_polygon = fix_geometry(st.session_state.gdf_polygon)
                return f"Berhasil mengekstrak {len(coords)} titik dan membentuk polygon ✅ (metode: {', '.join(tried)})", True
            else:
                st.session_state.gdf_polygon = None
                return "Koordinat terbaca, tetapi polygon tidak valid — hanya titik disimpan.", False
        else:
            return "Tidak ada koordinat ditemukan dalam PDF.", False
    
    elif uploaded.name.lower().endswith(".zip"):
        with tempfile.TemporaryDirectory() as tmp:
            zf = zipfile.ZipFile(io.BytesIO(uploaded.read()))
            zf.extractall(tmp)
            for root, _, files in os.walk(tmp):
                for f in files:
                    if f.lower().endswith(".shp"):
                        try:
                            st.session_state.gdf_polygon = gpd.read_file(os.path.join(root, f))
                            st.session_state.gdf_polygon = fix_geometry(st.session_state.gdf_polygon)
                            return "Shapefile PKKPR berhasil dimuat ✅", True
                        except Exception:
                            pass
        return "ZIP tidak berisi shapefile yang valid.", False

def process_tapak_file(uploaded_tapak):
    """Process tapak file dan simpan ke session state"""
    with tempfile.TemporaryDirectory() as tmp:
        zf = zipfile.ZipFile(io.BytesIO(uploaded_tapak.read()))
        zf.extractall(tmp)
        for root, _, files in os.walk(tmp):
            for f in files:
                if f.lower().endswith(".shp"):
                    try:
                        st.session_state.gdf_tapak = gpd.read_file(os.path.join(root, f))
                        st.session_state.gdf_tapak = fix_geometry(st.session_state.gdf_tapak)
                        return True
                    except Exception:
                        pass
    return False

# ======================
# UI: Upload PKKPR
# ======================
st.subheader("📄 Upload Dokumen PKKPR (PDF atau SHP ZIP)")
col1, col2 = st.columns([3, 2])

with col1:
    uploaded = st.file_uploader(
        "Unggah file PKKPR", 
        type=["pdf", "zip"], 
        label_visibility="collapsed",
        key="pkkpr_uploader"
    )

with col2:
    st.write("Parser membaca tabel koordinat (Bujur/Lintang, Longitude/Latitude, atau X/Y).")

# Tombol untuk memproses file
if uploaded and (st.session_state.uploaded_file_name != uploaded.name):
    with st.spinner("Memproses file PKKPR..."):
        result_msg, success = process_pkkpr_file(uploaded)
        if success:
            st.success(result_msg)
            st.session_state.uploaded_file_name = uploaded.name
        else:
            st.warning(result_msg)

# Tampilkan data jika ada di session state
if st.session_state.gdf_polygon is not None:
    display_shapefile_table(st.session_state.gdf_polygon, "PKKPR")
    if st.session_state.gdf_points is not None and not st.session_state.gdf_points.empty:
        display_shapefile_table(st.session_state.gdf_points, "PKKPR Points")

# ======================
# ANALISIS LUAS
# ======================
if st.session_state.gdf_polygon is not None:
    st.subheader("📏 Analisis Luas")
    centroid = st.session_state.gdf_polygon.to_crs(epsg=4326).geometry.centroid.iloc[0]
    utm_epsg, utm_zone = get_utm_info(centroid.x, centroid.y)
    luas_utm = st.session_state.gdf_polygon.to_crs(epsg=utm_epsg).area.sum()
    luas_merc = st.session_state.gdf_polygon.to_crs(epsg=3857).area.sum()

    st.write(f"Luas UTM {utm_zone}: {format_angka_id(luas_utm)} m²")
    st.write(f"Luas Mercator: {format_angka_id(luas_merc)} m²")
    if st.session_state.luas_pkkpr_doc:
        st.write(f"Luas dokumen: {st.session_state.luas_pkkpr_doc}")

    zip_bytes = save_shapefile_layers(st.session_state.gdf_polygon, st.session_state.gdf_points)
    st.download_button(
        "⬇️ Download SHP PKKPR", 
        zip_bytes, 
        "PKKPR_Hasil.zip", 
        mime="application/zip",
        key="download_pkkpr_shp"
    )

# ======================
# UPLOAD TAPAK
# ======================
st.subheader("🏗️ Upload Shapefile Tapak Proyek (ZIP)")
uploaded_tapak = st.file_uploader(
    "Unggah Tapak Proyek", 
    type=["zip"], 
    key="tapak_uploader"
)

# Tombol untuk memproses tapak
if uploaded_tapak and (st.session_state.uploaded_tapak_name != uploaded_tapak.name):
    with st.spinner("Memproses file tapak..."):
        success = process_tapak_file(uploaded_tapak)
        if success:
            st.success("Tapak berhasil dimuat ✅")
            st.session_state.uploaded_tapak_name = uploaded_tapak.name
        else:
            st.warning("Gagal memuat shapefile tapak.")

# Tampilkan data tapak jika ada
if st.session_state.gdf_tapak is not None:
    display_shapefile_table(st.session_state.gdf_tapak, "Tapak Proyek")

# ======================
# ANALISIS OVERLAY
# ======================
if st.session_state.gdf_polygon is not None and st.session_state.gdf_tapak is not None:
    st.subheader("📊 Analisis Overlay")
    centroid = st.session_state.gdf_polygon.to_crs(epsg=4326).geometry.centroid.iloc[0]
    utm_epsg, utm_zone = get_utm_info(centroid.x, centroid.y)
    gdf_tapak_utm = st.session_state.gdf_tapak.to_crs(utm_epsg)
    luas_tapak = gdf_tapak_utm.area.sum()
    gdf_pkkpr_utm = st.session_state.gdf_polygon.to_crs(utm_epsg)
    
    try:
        inter = gpd.overlay(gdf_tapak_utm, gdf_pkkpr_utm, how="intersection")
        luas_overlap = inter.area.sum()
    except Exception:
        luas_overlap = 0
    
    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Luas Tapak", f"{format_angka_id(luas_tapak)} m²")
    with col2:
        st.metric("Di dalam PKKPR", f"{format_angka_id(luas_overlap)} m²")
    with col3:
        st.metric("Di luar PKKPR", f"{format_angka_id(luas_tapak - luas_overlap)} m²")

# ======================
# PREVIEW PETA
# ======================
if st.session_state.gdf_polygon is not None:
    st.subheader("🌍 Preview Peta Interaktif")
    
    # Gunakan cached map creation
    @st.cache_data(ttl=600, show_spinner=False)
    def create_map(gdf_polygon, gdf_points, gdf_tapak):
        centroid = gdf_polygon.to_crs(epsg=4326).geometry.centroid.iloc[0]
        m = folium.Map(location=[centroid.y, centroid.x], zoom_start=17, tiles=None)
        Fullscreen(position="bottomleft").add_to(m)
        folium.TileLayer("openstreetmap").add_to(m)
        folium.TileLayer("CartoDB Positron").add_to(m)
        folium.TileLayer(xyz.Esri.WorldImagery).add_to(m)
        folium.GeoJson(gdf_polygon.to_crs(4326),
                       name="PKKPR",
                       style_function=lambda x: {"color":"yellow","weight":3,"fillOpacity":0.1}).add_to(m)
        if gdf_points is not None:
            for i, row in gdf_points.iterrows():
                folium.CircleMarker([row.geometry.y, row.geometry.x],
                                    radius=4, color="black", fill=True,
                                    fill_color="orange",
                                    popup=f"Titik {i+1}").add_to(m)
        if gdf_tapak is not None:
            folium.GeoJson(gdf_tapak.to_crs(4326),
                           name="Tapak Proyek",
                           style_function=lambda x: {"color":"red","fillColor":"red","fillOpacity":0.4}).add_to(m)
        folium.LayerControl().add_to(m)
        return m
    
    m = create_map(
        st.session_state.gdf_polygon, 
        st.session_state.gdf_points, 
        st.session_state.gdf_tapak
    )
    st_folium(m, width=900, height=600, key="map_view")

# =====================================================
# Layout PNG dengan caching
# =====================================================
if st.session_state.gdf_polygon is not None:
    st.subheader("🖼️ Export Peta PNG")
    
    @st.cache_data(ttl=600, show_spinner=False)
    def create_png_map(gdf_polygon, gdf_points, gdf_tapak):
        try:
            gdf_poly_3857 = gdf_polygon.to_crs(epsg=3857)
            
            try:
                total_area = gdf_poly_3857.area.sum()
            except Exception:
                total_area = 0
            if total_area > 0 and total_area < 5000:
                gdf_poly_3857["geometry"] = gdf_poly_3857.geometry.buffer(10)
            
            xmin, ymin, xmax, ymax = gdf_poly_3857.total_bounds
            fig, ax = plt.subplots(figsize=(10, 10), dpi=150)
            gdf_poly_3857.plot(ax=ax, facecolor="none", edgecolor="yellow", linewidth=2.5)
            
            if gdf_tapak is not None:
                try:
                    gdf_tapak.to_crs(epsg=3857).plot(ax=ax, facecolor="red", alpha=0.4)
                except Exception:
                    try:
                        gdf_tapak.plot(ax=ax, facecolor="red", alpha=0.4)
                    except Exception:
                        pass
            
            if gdf_points is not None and not gdf_points.empty:
                try:
                    gdf_points.to_crs(epsg=3857).plot(ax=ax, color="orange", markersize=20)
                except Exception:
                    try:
                        gdf_points.plot(ax=ax, color="orange", markersize=20)
                    except Exception:
                        pass
            
            basemap_drawn = False
            try:
                try:
                    zoom = ctx.calculate_zoom(gdf_poly_3857.total_bounds, ax.figure.get_size_inches()[0] * 100)
                except Exception:
                    zoom = None
                if zoom is not None:
                    zoom = int(min(zoom, 19))
                try:
                    if zoom is not None:
                        ctx.add_basemap(ax, crs=3857, source=ctx.providers.Esri.WorldImagery, zoom=zoom)
                    else:
                        ctx.add_basemap(ax, crs=3857, source=ctx.providers.Esri.WorldImagery)
                    basemap_drawn = True
                except Exception:
                    try:
                        fallback_zoom = 17 if zoom is None else int(min(zoom, 17))
                        ctx.add_basemap(ax, crs=3857, source=ctx.providers.OpenStreetMap.Mapnik, zoom=fallback_zoom)
                        basemap_drawn = True
                    except Exception:
                        ax.set_facecolor("#dcdcdc")
                        ax.text(
                            0.01, 0.01, "Basemap not available",
                            transform=ax.transAxes, fontsize=8, color="gray",
                            bbox=dict(facecolor="white", alpha=0.6, edgecolor="none")
                        )
            except Exception:
                ax.set_facecolor("#dcdcdc")
                ax.text(
                    0.01, 0.01, "Basemap not available",
                    transform=ax.transAxes, fontsize=8, color="gray",
                    bbox=dict(facecolor="white", alpha=0.6, edgecolor="none")
                )
            
            ax.set_xlim(xmin - (xmax - xmin) * 0.05, xmax + (xmax - xmin) * 0.05)
            ax.set_ylim(ymin - (ymax - ymin) * 0.05, ymax + (ymax - ymin) * 0.05)
            ax.set_title("Peta Kesesuaian Tapak Proyek dengan PKKPR", fontsize=14)
            ax.axis("off")
            
            legend_elements = [
                mpatches.Patch(facecolor="none", edgecolor="yellow", linewidth=2, label="PKKPR (Polygon)"),
                mpatches.Patch(facecolor="red", edgecolor="red", alpha=0.4, label="Tapak Proyek"),
                mlines.Line2D([], [], color="orange", marker="o", markeredgecolor="black", linestyle="None",
                              markersize=8, label="PKKPR (Titik)")
            ]
            ax.legend(
                handles=legend_elements,
                loc="upper right",
                fontsize=9,
                frameon=True,
                facecolor="white",
                edgecolor="black",
                title="Keterangan",
                title_fontsize=9
            )
            
            buf = io.BytesIO()
            plt.savefig(buf, format="png", bbox_inches="tight", dpi=200)
            buf.seek(0)
            plt.close(fig)
            return buf
        except Exception as e:
            return None
    
    png_buf = create_png_map(
        st.session_state.gdf_polygon, 
        st.session_state.gdf_points, 
        st.session_state.gdf_tapak
    )
    
    if png_buf:
        st.download_button(
            "⬇️ Download Peta PNG", 
            data=png_buf, 
            file_name="Peta_Overlay.png", 
            mime="image/png",
            key="download_png_map"
        )
    else:
        st.warning("Gagal membuat peta PNG.")

# ======================
# TOMBOL RESET
# ======================
st.sidebar.markdown("---")
if st.sidebar.button("🔄 Reset Semua Data", type="secondary"):
    for key in ['gdf_polygon', 'gdf_points', 'gdf_tapak', 'luas_pkkpr_doc', 
                'uploaded_file_name', 'uploaded_tapak_name']:
        if key in st.session_state:
            del st.session_state[key]
    st.rerun()

# ======================
# FOOTER
# ======================
st.markdown("---")
st.caption("© 2023 - PKKPR Converter & Overlay Tool - Optimized Version")
