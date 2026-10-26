"""Typed contracts shared by workers, coordinator, and verifier."""
from enum import StrEnum
from pydantic import BaseModel, ConfigDict, Field, model_validator


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


class Action(Record):
    op: str
    target: str = "root"
    guidance: str = ""
    source: str | None = None
    explorer_count: int = Field(default=1, ge=1, le=15)

    @model_validator(mode='before')
    @classmethod
    def _null_means_default(cls, data):
        # Models often emit explicit nulls for optional fields; treat them as omitted.
        if isinstance(data, dict):
            return {k: v for k, v in data.items() if v is not None or k == 'source'}
        return data


class Decision(Record):
    decision: str = "ACT"
    diagnosis: str = ""
    actions: list[Action] = Field(default_factory=list)


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


class Check(Record):
    ok: bool
    closed: list[str] = Field(default_factory=list)
    open: list[str] = Field(default_factory=list)
    inspections: list[Inspection] = Field(default_factory=list)
    output: str = ""


class Result(Record):
    status: Status
    run_dir: str
    revision: int
    output_tokens: int
    detail: str = ""
