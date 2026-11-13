# Article source

Read the [compiled PDF](green64.pdf) (83 pages).

For a short conceptual overview, read the [proof idea](../docs/proof-idea.md).
The [development timeline](../TIMELINE.md) records the project milestones;
[verification results](../VERIFICATION.md) describe the successful formal checks.

The [PDF-only expert review report](PDF_REVIEW.md) records the subsequent
whole-manuscript reviews and repairs. [PDF_BUILD.json](PDF_BUILD.json) records
the exact article inputs and PDF checksum.
The [exposition revision report](REVISION.md) records the reader's objections,
the mathematical repairs, and the checks performed on the revised article.

`main.tex` is the article entry point. The mathematical sections are included
as ordinary TeX files under `sections/`, so the article can be compiled without
Pandoc or the Markdown files:

```sh
bash build.sh
```

This uses local XeLaTeX with standard TeX Live packages and the TeX Gyre Pagella,
TeX Gyre Pagella Math and DejaVu Sans Mono fonts. It writes `green64.pdf` and
keeps temporary output in `build/`. Shell escape is disabled.

To regenerate the sections from the accompanying Markdown, run:

```sh
python3 from_markdown.py
bash build.sh
```

Regeneration needs Python 3 and Pandoc. It converts chapter links to internal
references and moves detailed source tables to an appendix. It checks that
every mathematical expression parsed from the Markdown occurs unchanged in
the generated sections. `CONVERSION.json` records the source and generated
file hashes. This check establishes conversion fidelity; the source guide
and the Lean verification record establish the separate connection to the
formal proof.

The article is prepared locally. No Overleaf project or public upload is
created by these commands.
