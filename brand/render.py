"""Write the brand files from brand/mark.svg and the vendored DM Mono Medium.

brand/mark.svg is the one drawn source: the exec pin as a shell prompt on the Blueprint
editor's graph canvas. This script composes the README lockup, the mark beside the command
set in DM Mono Medium, on GitHub's light and dark text colours, and the 1280 by 640 social
preview. Every wordmark is shaped with HarfBuzz and outlined, so no renderer needs the font
installed, and resvg renders the PNGs. Run it from the repository root as

    uv run --no-project --with resvg-py --with fonttools --with uharfbuzz python brand/render.py

It writes brand/lockup-light.svg and brand/lockup-dark.svg with their 4x PNGs, brand/mark.png
at 512 and brand/social.png.
"""

import math
import struct
from pathlib import Path

import resvg_py
import uharfbuzz
from fontTools.pens.boundsPen import BoundsPen
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen
from fontTools.ttLib import TTFont

BRAND = Path(__file__).resolve().parent
FONT = BRAND / "fonts/DMMono-Medium.ttf"
# Kerning and ligatures, as a browser applies them.
FEATURES = {"kern": True, "liga": True}
# The wordmark's tracking in em, as the review page set it.
TRACKING = -0.01
COMMAND = "bp-inspect"
# The mark is a 64 box with an 8 margin on each side for its shadow.
MARK_BOX = 64
MARK_MARGIN = 8
# The lockup's wordmark size and the gap between the box and the wordmark, for a 64 box.
LOCKUP_FONT = 41
LOCKUP_GAP = 17
# GitHub's text colours, so the lockup matches the README around it.
INKS = {"light": "#1f2328", "dark": "#f0f6fc"}
# The social preview: the graph canvas with a coarser grid, the lockup at 2.5x, a tagline and
# the repository address.
SOCIAL_WIDTH, SOCIAL_HEIGHT = 1280, 640
SOCIAL_SCALE = 2.5
SOCIAL_LEFT = 112
TAGLINE = ("Readable pseudocode, components and diffs", "from Blueprint .uasset files, without the editor.")
TAGLINE_FONT = 30
REPO = "github.com/MarcedForLife/UnrealBPInspect"
REPO_FONT = 22


def _number(value):
    text = f"{value:.2f}".rstrip("0").rstrip(".")
    return "0" if text == "-0" else text


class Wordmark:
    """Shapes text in the vendored font and outlines it as SVG paths."""

    def __init__(self):
        self.font = TTFont(FONT)
        self.shaper = uharfbuzz.Font(uharfbuzz.Face(FONT.read_bytes()))
        self.glyphs = self.font.getGlyphSet()
        self.names = self.font.getGlyphOrder()
        self.units = self.font["head"].unitsPerEm
        ascent, descent = self.font["hhea"].ascent, self.font["hhea"].descent
        # Where the baseline falls in a line box one em tall, as a browser places it.
        self.baseline_ratio = ascent / (ascent - descent)

    def outline(self, text, size):
        """Return the text as one path's commands and the x where its ink ends."""
        buffer = uharfbuzz.Buffer()
        buffer.add_str(text)
        buffer.guess_segment_properties()
        uharfbuzz.shape(self.shaper, buffer, FEATURES)
        scale = size / self.units
        path = SVGPathPen(self.glyphs, ntos=_number)
        bounds = BoundsPen(self.glyphs)
        x = 0.0
        for info, position in zip(buffer.glyph_infos, buffer.glyph_positions, strict=True):
            offset = ((x + position.x_offset) * scale, -position.y_offset * scale)
            transform = (scale, 0, 0, -scale, *offset)
            glyph = self.glyphs[self.names[info.codepoint]]
            glyph.draw(TransformPen(path, transform))
            glyph.draw(TransformPen(bounds, transform))
            x += position.x_advance + TRACKING * self.units
        return path.getCommands(), bounds.bounds[2]

    def path(self, text, size, x, top, ink, opacity=None):
        """Return a path element for text whose line box starts at top, and the x its ink ends."""
        commands, end = self.outline(text, size)
        baseline = top + size * self.baseline_ratio
        alpha = "" if opacity is None else f' fill-opacity="{opacity}"'
        element = (
            f'<path transform="translate({_number(x)} {_number(baseline)})" fill="{ink}"{alpha} '
            f'd="{commands}"/>'
        )
        return element, x + end


def _mark_parts():
    """Return the mark's defs and drawing, without its svg element, for inlining."""
    source = (BRAND / "mark.svg").read_text()
    defs = source[source.index("<defs>") + len("<defs>"):source.index("</defs>")]
    drawing = source[source.index("</defs>") + len("</defs>"):source.rindex("</svg>")]
    return defs.strip("\n"), drawing.strip("\n")


def _svg(width, height, defs, body):
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
        f'width="{width}" height="{height}">\n<defs>\n{defs}\n</defs>\n{body}\n</svg>\n'
    )


def _lockup(wordmark, ink):
    """Return the README lockup for one ink, and its width."""
    defs, drawing = _mark_parts()
    size = MARK_BOX + 2 * MARK_MARGIN
    text_x = MARK_MARGIN + MARK_BOX + LOCKUP_GAP
    top = MARK_MARGIN + (MARK_BOX - LOCKUP_FONT) / 2
    text, end = wordmark.path(COMMAND, LOCKUP_FONT, text_x, top, ink)
    width = math.ceil(end + MARK_MARGIN)
    body = f'<g transform="translate({MARK_MARGIN} {MARK_MARGIN})">\n{drawing}\n</g>\n{text}'
    return _svg(width, size, defs, body), width


def _social(wordmark):
    """Return the social preview card."""
    defs, drawing = _mark_parts()
    grid = (
        '    <pattern id="card-grid" width="64" height="64" patternUnits="userSpaceOnUse" '
        'patternTransform="translate(32 32)">\n'
        '      <path d="M64 0H0V64" fill="none" stroke="#fff" stroke-opacity=".07" stroke-width="2"/>\n'
        "    </pattern>"
    )
    box = MARK_BOX * SOCIAL_SCALE
    font = LOCKUP_FONT * SOCIAL_SCALE
    line_gap = 12
    block = box + 40 + TAGLINE_FONT * 2 + line_gap + 36 + REPO_FONT
    top = (SOCIAL_HEIGHT - block) / 2
    parts = [
        f'<rect width="{SOCIAL_WIDTH}" height="{SOCIAL_HEIGHT}" fill="#232323"/>',
        f'<rect width="{SOCIAL_WIDTH}" height="{SOCIAL_HEIGHT}" fill="url(#card-grid)"/>',
        f'<g transform="translate({SOCIAL_LEFT} {_number(top)}) scale({SOCIAL_SCALE})">\n{drawing}\n</g>',
    ]
    text_x = SOCIAL_LEFT + box + LOCKUP_GAP * SOCIAL_SCALE
    parts.append(wordmark.path(COMMAND, font, text_x, top + (box - font) / 2, "#ffffff")[0])
    line_top = top + box + 40
    for line in TAGLINE:
        parts.append(wordmark.path(line, TAGLINE_FONT, SOCIAL_LEFT, line_top, "#f0f6fc", ".72")[0])
        line_top += TAGLINE_FONT + line_gap
    parts.append(wordmark.path(REPO, REPO_FONT, SOCIAL_LEFT, line_top - line_gap + 36, "#f0f6fc", ".5")[0])
    return _svg(SOCIAL_WIDTH, SOCIAL_HEIGHT, grid + "\n" + defs, "\n".join(parts))


def _png(svg, path, zoom, expected):
    """Render the SVG at a zoom and check the PNG's pixel size, so a bad source cannot ship."""
    png = resvg_py.svg_to_bytes(svg_string=svg, zoom=zoom)
    width, height = struct.unpack(">II", png[16:24])
    if (width, height) != expected:
        raise ValueError(f"{path.name} rendered at {width} by {height}, expected {expected}")
    path.write_bytes(png)


def main():
    wordmark = Wordmark()
    mark_size = MARK_BOX + 2 * MARK_MARGIN
    _png((BRAND / "mark.svg").read_text(), BRAND / "mark.png", 512 / mark_size, (512, 512))
    for ground, ink in INKS.items():
        svg, width = _lockup(wordmark, ink)
        (BRAND / f"lockup-{ground}.svg").write_text(svg)
        _png(svg, BRAND / f"lockup-{ground}.png", 4, (width * 4, mark_size * 4))
    _png(_social(wordmark), BRAND / "social.png", 1, (SOCIAL_WIDTH, SOCIAL_HEIGHT))
    print(f"Wrote the lockups, mark.png and social.png into {BRAND.name}/")


if __name__ == "__main__":
    main()
