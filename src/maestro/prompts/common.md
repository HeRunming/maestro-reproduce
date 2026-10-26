# MAESTRO role prompts

These are engineering adaptations of arXiv:2610.25920 Appendix E, not verbatim
original prompts. Tool names and output fields match this implementation.

All roles: frozen imports, definitions, hypotheses and root signatures are immutable.
Only theorem declarations in MAESTRO GENERATED regions may change. No new axioms,
opaque values, custom elaborators or unsafe proof shortcuts. Lean is authoritative.
Compiling scaffolds containing sorry does not establish their mathematical truth.
Return a single JSON object at completion. Use tools while investigating.
