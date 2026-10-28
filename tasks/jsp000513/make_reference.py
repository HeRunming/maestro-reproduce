"""Build reference.tex (paper body without figure code) from the arXiv source.

The paper (arXiv:1806.03880) is under arXiv's non-exclusive distribution license, so
its text is not committed. Download the source first:
    mkdir -p vendor/jsp-awards-src/paper/src && cd vendor/jsp-awards-src/paper/src
    curl -L https://export.arxiv.org/e-print/1806.03880 | tar xz
then run: python3 tasks/jsp000513/make_reference.py
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
tex = (ROOT / 'vendor/jsp-awards-src/paper/src/dhs-aic.tex').read_text()
body = tex[tex.index(r'\begin{abstract}'):tex.index(r'\bibliographystyle')]
body = re.sub(r'\\begin\{figure\}.*?\\end\{figure\}',
              '[figure omitted; the text defines every graph and list]', body, flags=re.S)
body = re.sub(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}', '', body, flags=re.S)
body = re.sub(r'(?m)^\s*%.*\n', '', body)
body = re.sub(r'\n{3,}', '\n\n', body)
head = ('Dvořák, Hu, Sereni, "A 4-choosable graph that is not (8:2)-choosable", '
        'Advances in Combinatorics 2019:5, arXiv:1806.03880. LaTeX body (figures removed).\n\n')
(Path(__file__).parent / 'reference.tex').write_text(head + body)
