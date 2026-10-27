"""Typed contracts shared by workers, coordinator, and verifier."""
from enum import StrEnum
from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator


class Record(BaseModel):
    model_config = ConfigDict(extra="forbid")


class Status(StrEnum):
    PROVED = "proved"
    FALSIFIED = "falsified"
    BUDGET = "budget_exhausted"
    CANCELLED = "cancelled"
    ERROR = "infrastructure_error"


class Diagnosis(Record):
    outcome: str = "stuck_hard"
    detail: str
    failure_scope: str = "uncertain"
    approaches_tried: list[str] = Field(default_factory=list)
    repair_target: str | None = None
    repair_proposal: str | None = None
    witness: str | None = None


class Lenient(BaseModel):
    """Model-authored records: unknown keys ignored, explicit nulls mean 'use the default'."""
    model_config = ConfigDict(extra="ignore")

    @model_validator(mode='before')
    @classmethod
    def _null_means_default(cls, data):
        if isinstance(data, dict):
            return {k: v for k, v in data.items() if v is not None}
        return data


class Action(Lenient):
    op: str
    target: str = "root"
    targets: list[str] = Field(default_factory=list)
    guidance: str = ""
    source: str | None = None
    explorer_count: int = 1

    @field_validator('op', mode='before')
    @classmethod
    def _upper(cls, v):
        return v.strip().upper() if isinstance(v, str) else v

    @field_validator('explorer_count', mode='before')
    @classmethod
    def _clamp(cls, v):
        try:
            return min(max(int(v), 1), 15)
        except (TypeError, ValueError):
            return 1


class Decision(Lenient):
    decision: str = "ACT"
    diagnosis: str = ""
    actions: list[Action] = Field(default_factory=list)

    @field_validator('decision', mode='before')
    @classmethod
    def _upper(cls, v):
        return v.strip().upper() if isinstance(v, str) else v


class Event(Record):
    kind: str
    worker_id: str
    goal: str
    revision: int
    payload: dict = Field(default_factory=dict)


class Goal(Record):
    name: str
    signature: str
    proof: str = "by\n  sorry"
    parent: str | None = None


class Inspection(Record):
    name: str
    type: str
    axioms: list[str]
    is_theorem: bool
    direct_sorry: bool = False
    type_hash: str = ""


class Check(Record):
    ok: bool
    closed: list[str] = Field(default_factory=list)
    open: list[str] = Field(default_factory=list)
    # Open goals whose own proof contains sorry (the ones a prover should attack).
    frontier: list[str] = Field(default_factory=list)
    inspections: list[Inspection] = Field(default_factory=list)
    output: str = ""


class Result(Record):
    status: Status
    run_dir: str
    revision: int
    output_tokens: int
    detail: str = ""
