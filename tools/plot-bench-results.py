"""Plots hash throughput from the CSV written by `cargo bench --bench speed -- out.csv`.

Usage: python tools/plot-bench-results.py out.csv [machine name] [image path]

With an image path the plot is saved there at high resolution instead of shown.
"""

import sys

import matplotlib.pyplot as plt
import polars as pl
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedLocator, FuncFormatter

COLORS = ["#4477aa", "#ee6677", "#228833", "#ccbb44", "#66ccee", "#aa3377"]
MARKERS = ["o", "s", "^", "D", "v", "P"]

# Legend groups by security guarantee, each with its own line style and opacity.
# Hashes not listed here fall in the last group.
GROUPS = [
    ("~128 bit", "-", 1.0),
    ("~64 bit", "--", 1.0),
    ("Insecure", ":", 0.5),
]
GUARANTEE = {
    "polyxor128": "~128 bit",
    "polyxor128-mac": "~128 bit",
    "polyval": "~128 bit",
    "poly1305": "~128 bit",  # Really ~106 bit.
    "aegis-128l-mac": "~128 bit",
    "blake3": "~128 bit",
    "siphash2-4": "~64 bit",
    "polymur-hash": "~64 bit",
    "sha1": "~64 bit",  # Collisions cost ~2^63.
}


def format_bytes(x, _pos):
    for unit in ["B", "KiB", "MiB", "GiB"]:
        if x < 1024:
            return f"{x:g} {unit}"
        x /= 1024
    return f"{x:g} TiB"


def main():
    df = pl.read_csv(sys.argv[1]).with_columns(gbps=pl.col("bytes") / pl.col("ns"))
    # Alphabetical, except PolyXOR128 first.
    pinned = ["polyxor128", "polyxor128-mac"]
    hashes = sorted(
        df["hash"].unique().to_list(),
        key=lambda h: (pinned.index(h) if h in pinned else len(pinned), h),
    )

    def group_of(h):
        return GUARANTEE.get(h, GROUPS[-1][0])

    fig, ax = plt.subplots(figsize=(11, 6.5), layout="constrained")
    fig.get_layout_engine().set(w_pad=0.25, h_pad=0.25)
    lines = {}
    for group, linestyle, alpha in GROUPS:
        for i, name in enumerate(h for h in hashes if group_of(h) == group):
            d = df.filter(pl.col("hash") == name).sort("bytes")
            (lines[name],) = ax.plot(
                d["bytes"],
                d["gbps"],
                color=COLORS[i % len(COLORS)],
                linestyle=linestyle,
                linewidth=2,
                alpha=alpha,
                marker=MARKERS[i % len(MARKERS)],
                markersize=6,
                markeredgecolor="#fcfcfb",
                markeredgewidth=1,
                # Staggered so markers of lines that coincide don't stack.
                markevery=(i % 4, 4),
            )

    sizes = sorted(df["bytes"].unique().to_list())
    ax.set_xscale("log", base=2)
    ax.xaxis.set_major_locator(FixedLocator(sizes[::2]))
    ax.xaxis.set_major_formatter(FuncFormatter(format_bytes))
    ax.xaxis.set_minor_locator(FixedLocator([]))
    ax.set_xlim(sizes[0], sizes[-1])
    ax.set_ylim(bottom=0)

    ax.set_xlabel("Input size", color="#52514e")
    ax.set_ylabel("Throughput (GB/s)", color="#52514e")
    title = "Hash throughput by input size"
    if len(sys.argv) > 2:
        title += f" ({sys.argv[2]})"
    ax.set_title(title, loc="left", color="#0b0b0b")
    ax.grid(True, color="#e1e0d9", linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ["top", "right"]:
        ax.spines[side].set_visible(False)
    for side in ["left", "bottom"]:
        ax.spines[side].set_color("#c3c2b7")
    ax.tick_params(colors="#898781", labelcolor="#52514e")

    # One legend section per line style.
    handles, labels, headers = [], [], []
    for title, _, _ in GROUPS:
        names = [h for h in hashes if group_of(h) == title]
        if handles:
            handles.append(Line2D([], [], alpha=0))
            labels.append("")
        headers.append(len(labels))
        handles.append(Line2D([], [], alpha=0))
        labels.append(title)
        handles += [lines[h] for h in names]
        labels += names
    legend = ax.legend(
        handles,
        labels,
        loc="upper left",
        bbox_to_anchor=(1.01, 1),
        frameon=False,
        labelcolor="#52514e",
        # Markers at both ends so the line style shows in between.
        numpoints=2,
        handlelength=3.5,
    )
    for i in headers:
        legend.get_texts()[i].set(color="#0b0b0b", fontweight="bold")

    if len(sys.argv) > 3:
        fig.savefig(sys.argv[3], dpi=100)
    else:
        plt.show()


if __name__ == "__main__":
    main()
