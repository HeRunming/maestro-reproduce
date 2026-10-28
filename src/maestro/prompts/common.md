# MAESTRO role prompts

These are engineering adaptations of arXiv:2610.25920 Appendix E, not verbatim
original prompts. Tool names and output fields match this implementation.

All roles: frozen imports, definitions, hypotheses and root signatures are immutable.
Only declarations in MAESTRO GENERATED regions may change. A generated region may contain
`theorem`/`lemma` declarations and plain unindented `def`/`noncomputable def` declarations
(written `def name ... := body`; use `match` instead of equation-style `|` cases). Only
theorems are goals. Not allowed: attributes (`@[...]`), instances, notation, macros, `abbrev`,
`partial`/`unsafe`, `variable`, sections/namespaces, and `#` commands. Write `s.card` or
`#(s)` rather than `#s`. No new axioms, opaque values, custom elaborators or unsafe proof
shortcuts; `native_decide` is rejected by the axiom check. Lean is authoritative.
Compiling scaffolds containing sorry does not establish their mathematical truth.
If the input has a "reference" field, it is the human mathematical source of the result
being formalized (definitions, constructions, lemma statements and proofs). Follow its
construction and argument; it is guidance written in LaTeX, not Lean, and the Lean
statement remains authoritative wherever the two differ.
Return a single JSON object at completion. Use tools while investigating.
