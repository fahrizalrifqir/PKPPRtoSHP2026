import streamlit as st
import geopandas as gpd
import pandas as pd
import io, os, zipfile, tempfile, re, math
from shapely.geometry import Point, Polygon, MultiPolygon, GeometryCollection, MultiPoint, LineString
from shapely.validation import make_valid
import folium
from streamlit_folium import st_folium
import matplotlib.pyplot as plt
import contextily as ctx
from folium.plugins import Fullscreen
import xyzservices.providers as xyz
import matplotlib.patches as mpatches
import matplotlib.lines as mlines

st.set_page_config(
    page_title="PKKPR → SHP + Overlay (Final)",
    layout="wide",
    initial_sidebar_state="expanded"
)

st.title("PKKPR → Shapefile Converter & Overlay Tapak Proyek (Final)")
st.markdown("---")

if 'gdf_polygon' not in st.session_state:
    st.session_state.gdf_polygon = None
if 'gdf_points' not in st.session_state:
    st.session_state.gdf_points = None
if 'gdf_tapak' not in st.session_state:
    st.session_state.gdf_tapak = None
if 'uploaded_file_name' not in st.session_state:
    st.session_state.uploaded_file_name = None
if 'uploaded_tapak_name' not in st.session_state:
    st.session_state.uploaded_tapak_name = None

DEBUG = st.sidebar.checkbox("Tampilkan debug logs", value=False)

def format_angka_id(value):
    try:
        val = float(value)
        if abs(val - round(val)) < 0.001:
            return f"{int(round(val)):,}".replace(",", ".")
        s = f"{val:,.2f}"
        return s.replace(",", "X").replace(".", ",").replace("X", ".")
    except:
        return str(value)

def get_utm_info(lon, lat):
    zone = int((lon + 180) / 6) + 1
    epsg = 32600 + zone if lat >= 0 else 32700 + zone
    zone_label = f"{zone}{'N' if lat >= 0 else 'S'}"
    return epsg, zone_label

def fix_geometry(gdf):
    if gdf is None or gdf.empty:
        return gdf

    gdf["geometry"] = gdf["geometry"].apply(make_valid)

    def extract_valid(geom):
        if geom is None:
            return None
        if geom.geom_type == "GeometryCollection":
            polys = [g for g in geom.geoms if g.geom_type in ["Polygon", "MultiPolygon"]]
            if len(polys) == 1:
                return polys[0]
            elif polys:
                return MultiPolygon(polys)
            return None
        return geom

    gdf["geometry"] = gdf["geometry"].apply(extract_valid)
    return gdf

def display_shapefile_table(gdf, title):
    if gdf is None or gdf.empty:
        return

    st.write(f"**Tabel Data {title}**")
    st.caption(f"{len(gdf)} fitur, {len(gdf.columns)} kolom")

    display_df = gdf.copy()

    if "geometry" in display_df.columns:
        def format_geometry(geom):
            if geom is None:
                return None
            gt = geom.geom_type
            if gt == "Point":
                return f"Point ({geom.x:.6f}, {geom.y:.6f})"
            elif gt == "Polygon":
                return f"Polygon ({len(geom.exterior.coords)} titik)"
            elif gt == "MultiPolygon":
                return f"MultiPolygon ({len(geom.geoms)} polygon)"
            return gt

        display_df["geometry"] = display_df["geometry"].apply(format_geometry)

    st.dataframe(display_df, use_container_width=True, height=300)

    csv = display_df.to_csv(index=False).encode("utf-8")
    st.download_button(
        label=f"📥 Download CSV {title}",
        data=csv,
        file_name=f"{title.replace(' ', '_')}.csv",
        mime="text/csv"
    )

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

def validate_shapefile_zip(uploaded):
    with tempfile.TemporaryDirectory() as tmp:
        try:
            zf = zipfile.ZipFile(io.BytesIO(uploaded.read()))
            zf.extractall(tmp)
        except Exception:
            return None, "ZIP tidak valid"

        shp = None
        shx = False
        dbf = False

        for root, _, files in os.walk(tmp):
            for f in files:
                fl = f.lower()
                fp = os.path.join(root, f)

                if fl.endswith(".shp"):
                    shp = fp
                elif fl.endswith(".shx"):
                    shx = True
                elif fl.endswith(".dbf"):
                    dbf = True

        if not shp:
            return None, "File .shp tidak ditemukan"

        if not shx or not dbf:
            return None, "ZIP harus berisi .shp + .shx + .dbf"

        try:
            gdf = gpd.read_file(shp)
            return gdf, None
        except Exception as e:
            return None, str(e)

def process_pkkpr_file(uploaded):
    gdf, err = validate_shapefile_zip(uploaded)
    if err:
        return err, False

    st.session_state.gdf_polygon = fix_geometry(gdf)
    st.session_state.gdf_points = None
    return "Shapefile PKKPR berhasil dimuat ✅", True

def process_tapak_file(uploaded):
    gdf, err = validate_shapefile_zip(uploaded)
    if err:
        return False
    st.session_state.gdf_tapak = fix_geometry(gdf)
    return True

st.subheader("📄 Upload Dokumen PKKPR (SHP ZIP saja)")

uploaded = st.file_uploader(
    "Unggah file PKKPR",
    type=["zip"],
    key="pkkpr_uploader"
)

if uploaded and st.session_state.uploaded_file_name != uploaded.name:
    with st.spinner("Memproses shapefile PKKPR..."):
        msg, success = process_pkkpr_file(uploaded)
        if success:
            st.success(msg)
            st.session_state.uploaded_file_name = uploaded.name
        else:
            st.warning(msg)

if st.session_state.gdf_polygon is not None:
    display_shapefile_table(st.session_state.gdf_polygon, "PKKPR")

    centroid = st.session_state.gdf_polygon.to_crs(4326).geometry.centroid.iloc[0]
    utm_epsg, utm_zone = get_utm_info(centroid.x, centroid.y)

    luas_utm = st.session_state.gdf_polygon.to_crs(utm_epsg).area.sum()
    luas_merc = st.session_state.gdf_polygon.to_crs(3857).area.sum()

    st.subheader("📏 Analisis Luas")

    c1, c2 = st.columns(2)

    with c1:
        st.metric("Luas UTM", f"{format_angka_id(luas_utm)} m²", f"Zona {utm_zone}")

    with c2:
        st.metric("Luas Mercator", f"{format_angka_id(luas_merc)} m²")

    zip_bytes = save_shapefile_layers(st.session_state.gdf_polygon, st.session_state.gdf_points)

    st.download_button(
        "⬇️ Download SHP PKKPR",
        zip_bytes,
        "PKKPR_Hasil.zip",
        mime="application/zip"
    )

st.subheader("🏗️ Upload Shapefile Tapak Proyek (ZIP)")

uploaded_tapak = st.file_uploader(
    "Unggah Tapak Proyek",
    type=["zip"],
    key="tapak_uploader"
)

if uploaded_tapak and st.session_state.uploaded_tapak_name != uploaded_tapak.name:
    with st.spinner("Memproses tapak proyek..."):
        if process_tapak_file(uploaded_tapak):
            st.success("Tapak berhasil dimuat ✅")
            st.session_state.uploaded_tapak_name = uploaded_tapak.name
        else:
            st.warning("Gagal memuat shapefile tapak")

if st.session_state.gdf_tapak is not None:
    display_shapefile_table(st.session_state.gdf_tapak, "Tapak Proyek")

if st.session_state.gdf_polygon is not None and st.session_state.gdf_tapak is not None:
    st.subheader("📊 Analisis Overlay")

    centroid = st.session_state.gdf_polygon.to_crs(4326).geometry.centroid.iloc[0]
    utm_epsg, utm_zone = get_utm_info(centroid.x, centroid.y)

    gdf_tapak_utm = st.session_state.gdf_tapak.to_crs(utm_epsg)
    gdf_pkkpr_utm = st.session_state.gdf_polygon.to_crs(utm_epsg)

    luas_tapak = gdf_tapak_utm.area.sum()

    try:
        inter = gpd.overlay(gdf_tapak_utm, gdf_pkkpr_utm, how="intersection")
        luas_overlap = inter.area.sum()
    except:
        luas_overlap = 0

    luas_luar = luas_tapak - luas_overlap

    c1, c2, c3 = st.columns(3)

    with c1:
        st.metric("Luas Tapak", f"{format_angka_id(luas_tapak)} m²")

    with c2:
        st.metric("Di Dalam PKKPR", f"{format_angka_id(luas_overlap)} m²")

    with c3:
        st.metric("Di Luar PKKPR", f"{format_angka_id(luas_luar)} m²")

if st.session_state.gdf_polygon is not None:
    st.subheader("🌍 Preview Peta Interaktif")

    centroid = st.session_state.gdf_polygon.to_crs(4326).geometry.centroid.iloc[0]

    m = folium.Map(
        location=[centroid.y, centroid.x],
        zoom_start=17,
        tiles=None
    )

    Fullscreen(position="bottomleft").add_to(m)

    folium.TileLayer("openstreetmap").add_to(m)
    folium.TileLayer("CartoDB Positron").add_to(m)
    folium.TileLayer(xyz.Esri.WorldImagery).add_to(m)

    folium.GeoJson(
        st.session_state.gdf_polygon.to_crs(4326),
        name="PKKPR",
        style_function=lambda x: {
            "color": "yellow",
            "weight": 3,
            "fillColor": "yellow",
            "fillOpacity": 0.15
        }
    ).add_to(m)

    if st.session_state.gdf_tapak is not None:
        folium.GeoJson(
            st.session_state.gdf_tapak.to_crs(4326),
            name="Tapak",
            style_function=lambda x: {
                "color": "red",
                "weight": 2,
                "fillColor": "red",
                "fillOpacity": 0.35
            }
        ).add_to(m)

    folium.LayerControl().add_to(m)

    st_folium(m, width=1000, height=600)

if st.session_state.gdf_polygon is not None:
    st.subheader("🖼️ Export Peta PNG")

    if st.button("Buat Peta PNG"):
        with st.spinner("Membuat PNG..."):
            try:
                gdf_poly_3857 = st.session_state.gdf_polygon.to_crs(3857)
                xmin, ymin, xmax, ymax = gdf_poly_3857.total_bounds

                fig, ax = plt.subplots(figsize=(10, 10), dpi=150)

                providers = [
                    ctx.providers.Esri.WorldImagery,
                    ctx.providers.OpenStreetMap.Mapnik,
                    ctx.providers.CartoDB.Positron
                ]

                basemap_ok = False

                for provider in providers:
                    try:
                        ctx.add_basemap(
                            ax,
                            crs=gdf_poly_3857.crs,
                            source=provider,
                            zoom=17,
                            reset_extent=False
                        )
                        basemap_ok = True
                        break
                    except:
                        continue

                if not basemap_ok:
                    ax.set_facecolor("#dddddd")

                gdf_poly_3857.plot(
                    ax=ax,
                    facecolor="none",
                    edgecolor="yellow",
                    linewidth=2.5
                )

                if st.session_state.gdf_tapak is not None:
                    st.session_state.gdf_tapak.to_crs(3857).plot(
                        ax=ax,
                        facecolor="red",
                        alpha=0.4
                    )

                ax.set_xlim(xmin - 50, xmax + 50)
                ax.set_ylim(ymin - 50, ymax + 50)

                ax.axis("off")

                legend_elements = [
                    mpatches.Patch(facecolor="none", edgecolor="yellow", label="PKKPR"),
                    mpatches.Patch(facecolor="red", edgecolor="red", alpha=0.4, label="Tapak")
                ]

                ax.legend(handles=legend_elements)

                buf = io.BytesIO()
                plt.savefig(buf, format="png", bbox_inches="tight", dpi=200)
                buf.seek(0)
                plt.close(fig)

                st.download_button(
                    "⬇️ Download PNG",
                    buf,
                    "Peta_Overlay.png",
                    mime="image/png"
                )

            except Exception as e:
                st.error(str(e))

st.sidebar.markdown("---")

if st.sidebar.button("🔄 Reset Semua Data"):
    for key in list(st.session_state.keys()):
        del st.session_state[key]
    st.rerun()

st.sidebar.markdown("---")

if st.session_state.gdf_polygon is not None:
    st.sidebar.success("✓ PKKPR Dimuat")
else:
    st.sidebar.warning("Menunggu upload PKKPR")

if st.session_state.gdf_tapak is not None:
    st.sidebar.success("✓ Tapak Dimuat")

st.markdown("---")
st.caption("PKKPR Converter Stable Version")
