"""Runtime configuration. Secret values never belong in TOML."""
from pathlib import Path
import tomllib
from typing import Literal
from pydantic import Field
from .models import Record


class ProviderConfig(Record):
    protocol: Literal['anthropic', 'openai'] = 'anthropic'
    model: str = 'claude-opus-5-5'
    base_url: str | None = None
    key_env: str = 'ANTHROPIC_API_KEY'
    max_tokens: int = Field(default=16000, ge=128)
    effort: str = 'high'
    timeout: float = Field(default=900, gt=0)  # hard wall-clock limit per request attempt
    retries: int = Field(default=3, ge=0, le=10)


class MCPConfig(Record):
    enabled: bool = False
    command: list[str] = Field(default_factory=lambda: ['npx', '-y', '@leanprover/mcp-server-lean'])


class Config(Record):
    project: Path = Path('/data/hrm/lean_workspace')
    provider: ProviderConfig = Field(default_factory=ProviderConfig)
    mcp: MCPConfig = Field(default_factory=MCPConfig)
    concurrency: int = Field(default=3, ge=1, le=32)
    output_budget: int = Field(default=250000, ge=128)
    max_turns: int = Field(default=40, ge=1)
    max_events: int = Field(default=100, ge=1)
    wall_seconds: float = Field(default=3600, gt=0)
    compile_seconds: float = Field(default=120, gt=0)
    planner_rounds: int = Field(default=6, ge=1, le=6)
    explorer_cohort: int = Field(default=3, ge=1, le=15)
    mode: Literal['maestro', 'plain', 'naive'] = 'maestro'
    # Coordinator context: above this size it gets a declaration outline instead of the
    # full source, and its session is restarted (with recent decisions) past the second limit.
    coordinator_source_chars: int = Field(default=40000, ge=1000)
    coordinator_context_chars: int = Field(default=400000, ge=10000)
    # Testing knob: start with the planner instead of a prover (exercises decomposition).
    initial_role: Literal['prover', 'planner'] = 'prover'

    @classmethod
    def load(cls, path: Path):
        return cls.model_validate(tomllib.loads(path.read_text()))
