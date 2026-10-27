"""Frozen task regions and deliberately restricted generated declarations."""
import re
from dataclasses import dataclass
from pathlib import Path
from .models import Goal

START = "-- MAESTRO GENERATED BEGIN"
END = "-- MAESTRO GENERATED END"
# This is an input boundary scanner, not the proof-completion oracle.
TOKEN = re.compile(r'/\-|-/|--[^\n]*|"(?:\\.|[^"\\])*"', re.S)


def uncomment(text: str) -> str:
    out, pos, depth = [], 0, 0
    for m in TOKEN.finditer(text):
        if not depth:
            out.append(text[pos:m.start()])
        token = m.group()
        if token == '/-':
            depth += 1
        elif token == '-/' and depth:
            depth -= 1
        elif not depth and token.startswith('"'):
            out.append(token)
        pos = m.end()
    if depth:
        raise ValueError("unterminated Lean comment")
    out.append(text[pos:])
    return ''.join(out)


# `open` is allowed (proofs need `open Classical in`); the root's elaborated type is
# pinned by hash in Workspace, so opens cannot change what the root statement means.
SAFE_OPTIONS = r'(?:maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|synthInstance\.maxSize|linter\.[\w.]+|pp\.[\w.]+|trace\.[\w.]+)'
FORBIDDEN = re.compile(
    r'\b(import|namespace|end|section|axiom|constant|opaque|unsafe|partial|macro|elab|syntax|'
    r'initialize|attribute|run_tac|run_elab|run_cmd|run_meta|implemented_by|extern|def|abbrev|'
    r'instance|example|notation|infix|infixl|infixr|prefix|postfix|export|mutual|inductive|'
    r'structure|class|deriving|command|builtin_initialize|by_elab|local|scoped)\b'
    r'|\bset_option\s+(?!' + SAFE_OPTIONS + r'\b)'   # only whitelisted options
    r'|#'                                              # Lean commands
    r'|@\['                                            # attributes
    r'|\bLean\.'                                       # meta-level API
)
DECL = re.compile(r'(?m)^theorem\s+([A-Za-z_][\w\.]*)\b')


def assignment(text: str, start: int = 0) -> int:
    """Find declaration assignment outside binder/type parentheses and comments."""
    clean = re.sub(r'--[^\n]*|/\-.*?\-/', lambda m: ' ' * len(m[0]), text, flags=re.DOTALL)
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
    matches = list(DECL.finditer(clean))
    if not matches or clean[:matches[0].start()].strip():
        raise ValueError("generated region must contain only named theorem declarations")
    goals = []
    for i, match in enumerate(matches):
        chunk = clean[match.start():matches[i+1].start() if i+1 < len(matches) else len(clean)]
        # ':=' in binders/default values is intentionally unsupported in generated signatures.
        if ':=' not in chunk:
            raise ValueError("missing theorem proof")
        split = assignment(chunk)
        signature, proof = chunk[:split], chunk[split+2:]
        goals.append(Goal(name=match[1], signature=signature.strip(), proof=proof.strip()))
    if len({g.name for g in goals}) != len(goals):
        raise ValueError("duplicate theorem name")
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
