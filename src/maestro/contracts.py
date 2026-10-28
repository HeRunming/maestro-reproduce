"""Frozen task regions and deliberately restricted generated declarations."""
import re
from dataclasses import dataclass
from pathlib import Path
from .models import Goal

START = "-- MAESTRO GENERATED BEGIN"
END = "-- MAESTRO GENERATED END"
# This is an input boundary scanner, not the proof-completion oracle. It is a small Lean
# lexer: comments (nested), string, char and «quoted-name» literals are recognized with
# Lean's own precedence, so text that Lean compiles as code can never be classified as a
# comment. Literal forms it does not model (raw and interpolated strings) are rejected.
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'")
IDENT_TAIL = re.compile(r"[\w'!?₀-ₜᵢ-ᵪⱼ]")


def lex(text: str):
    """Yield (kind, start, end) spans: 'code', 'comment' or 'literal'."""
    i, n, depth, code = 0, len(text), 0, 0
    def flush(upto):
        return [('code', code, upto)] if upto > code else []
    while i < n:
        if depth:
            # Inside a block comment only nesting markers matter (no strings or chars).
            if text.startswith('/-', i):
                depth, i = depth + 1, i + 2
            elif text.startswith('-/', i):
                depth, i = depth - 1, i + 2
                if not depth:
                    yield ('comment', begin, i)
                    code = i
            else:
                i += 1
            continue
        if text.startswith('/-', i):
            yield from flush(i)
            depth, begin, i = 1, i, i + 2
            continue
        if text.startswith('--', i):
            yield from flush(i)
            j = text.find('\n', i)
            j = n if j < 0 else j
            yield ('comment', i, j)
            i = code = j
            continue
        c = text[i]
        prev = text[i - 1] if i else ''
        j = None
        if c == '"':
            if prev == '!' or re.search(r'(?<![\w.])r#*$', text[max(0, i - 8):i]):
                raise ValueError("raw or interpolated string literals are not supported")
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            if j >= n:
                raise ValueError("unterminated string literal")
            j += 1
        elif c == "'" and not IDENT_TAIL.match(prev):
            m = CHAR.match(text, i)
            j = m.end() if m else None
        elif c == '«':  # «quoted name»: opaque, may contain any character except »
            j = text.find('»', i)
            if j < 0:
                raise ValueError("unterminated «quoted name»")
            j += 1
        if j is None:
            i += 1
            continue
        yield from flush(i)
        yield ('literal', i, j)
        i = code = j
    if depth:
        raise ValueError("unterminated Lean comment")
    yield from flush(n)


def uncomment(text: str) -> str:
    return ''.join(text[a:b] for kind, a, b in lex(text) if kind != 'comment')


def mask(text: str) -> str:
    """Same length as text; comments and literal contents blanked (newlines kept)."""
    blank = lambda t: re.sub(r'[^\n]', ' ', t)
    return ''.join(text[a:b] if kind == 'code' else blank(text[a:b]) for kind, a, b in lex(text))


# `open` is allowed (proofs need `open Classical in`). Workspace pins the root's
# elaborated type hash, so an `open ... in` or a generated `def` that shadows a name
# cannot change what the root statement means.
SAFE_OPTIONS = r'(?:maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|synthInstance\.maxSize|linter\.[\w.]+|pp\.[\w.]+|trace\.[\w.]+)'
FORBIDDEN = re.compile(
    r'\b(import|namespace|end|section|axiom|constant|opaque|unsafe|partial|macro|elab|syntax|'
    r'initialize|attribute|run_tac|run_elab|run_cmd|run_meta|implemented_by|extern|abbrev|'
    r'instance|example|notation|infix|infixl|infixr|prefix|postfix|export|mutual|inductive|'
    r'structure|class|deriving|command|builtin_initialize|by_elab|local|scoped|variable|universe|'
    r'private|protected)\b'
    r'|\bset_option\s+(?!' + SAFE_OPTIONS + r'\b)'   # only whitelisted options
    r'|#[A-Za-z_]'                                     # Lean commands (#eval, #exit, ...)
    r'|@\['                                            # attributes
    r'|\bLean\.'                                       # meta-level API
)
DECL = re.compile(r'(?m)^theorem\s+([A-Za-z_][\w\.]*)\b')
# Generated regions accept theorems (`lemma` is Mathlib syntax for one) and plain data
# definitions. Definitions are never goals: closure is decided by the theorems' axioms.
GEN_DECL = re.compile(r'(?m)^(theorem|lemma|def|noncomputable\s+def)\s+([A-Za-z_][\w\.]*)\b')


def assignment(text: str, start: int = 0) -> int:
    """Find declaration assignment outside binder/type parentheses and comments."""
    clean = mask(text)
    depth = 0
    for i in range(start, len(clean) - 1):
        if clean[i] in '([{':
            depth += 1
        elif clean[i] in ')]}':
            depth -= 1
        elif clean[i:i+2] == ':=' and depth == 0:
            return i
    raise ValueError('missing theorem proof assignment')


def parse_goals(region: str) -> list[Goal]:
    clean = uncomment(region)
    if FORBIDDEN.search(clean):
        raise ValueError("unsupported or unsafe command in generated region")
    matches = list(GEN_DECL.finditer(clean))
    # `def`/`noncomputable` may appear only as the keyword of a top-level declaration.
    keywords = {m.start(1) + m[1].rfind('def') for m in matches if m[1] != 'theorem' and m[1] != 'lemma'}
    keywords |= {m.start(1) for m in matches if m[1].startswith('noncomputable')}
    stray = [m.start() for m in re.finditer(r'\b(def|noncomputable)\b', clean) if m.start() not in keywords]
    if stray:
        raise ValueError("`def` is only allowed as an unindented top-level declaration")
    if not matches or clean[:matches[0].start()].strip():
        raise ValueError("generated region must contain only named theorem and def declarations")
    goals = []
    for i, match in enumerate(matches):
        chunk = clean[match.start():matches[i+1].start() if i+1 < len(matches) else len(clean)]
        # ':=' in binders/default values is intentionally unsupported in generated signatures.
        # Definitions by pattern-matching equations need `:= match ... with` instead.
        if ':=' not in chunk:
            raise ValueError(f"missing ':=' in declaration {match[2]}")
        split = assignment(chunk)
        signature, proof = chunk[:split], chunk[split+2:]
        kind = 'theorem' if match[1] in ('theorem', 'lemma') else 'def'
        goals.append(Goal(name=match[2], signature=signature.strip(), proof=proof.strip(), kind=kind))
    if len({g.name for g in goals}) != len(goals):
        raise ValueError("duplicate declaration name")
    return goals


@dataclass(frozen=True)
class Contract:
    prefix: str
    suffix: str
    root: Goal

    @classmethod
    def load(cls, path: Path) -> 'Contract':
        text = path.read_text()
        clean = uncomment(text)
        matches = list(DECL.finditer(clean))
        if len(matches) != 1:
            raise ValueError("supported input: exactly one top-level theorem")
        # Locate the original declaration while retaining frozen comments/definitions.
        name = matches[0][1]
        original = re.search(r'(?m)^theorem\s+' + re.escape(name) + r'\b', text)
        if original is None:
            raise ValueError("unsupported theorem layout")
        a = assignment(text, original.start())
        tail = text[a+2:]
        boundary = re.search(r'(?m)^end\b', tail)
        proof = tail[:boundary.start()] if boundary else tail
        if uncomment(proof).strip() not in ('by\n  sorry', 'by sorry', 'sorry'):
            raise ValueError("input theorem must have a single sorry proof placeholder")
        signature = text[original.start():a].strip()
        return cls(text[:original.start()], tail[boundary.start():] if boundary else '', Goal(name=name, signature=signature))

    def render(self, region: str) -> str:
        return self.prefix + START + '\n' + region.strip() + '\n' + END + '\n' + self.suffix

    def validate(self, source: str) -> list[Goal]:
        before, sep, rest = source.partition(START + '\n')
        region, sep2, after = rest.partition('\n' + END + '\n')
        if not sep or not sep2 or before != self.prefix or after != self.suffix:
            raise ValueError("frozen context was modified")
        goals = parse_goals(region)
        root = next((g for g in goals if g.name == self.root.name), None)
        if root is None or root.signature != uncomment(self.root.signature).strip():
            raise ValueError("original root signature changed")
        return goals
