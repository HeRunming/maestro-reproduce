# Paper-to-code map

| Paper element | Implementation | Status / adaptation |
|---|---|---|
| §3.1 frozen task, versioned workspace | `contracts.py`, `workspace.py`, `journal.py` | Single root theorem supported; immutable revision snapshots and atomic CURRENT pointer. |
| §3.1 open obligations | `lean.py` + `Inspect.lean` | Native namespace resolution and transitive axiom collection, not regex. |
| §3.2 persistent coordinator | `engine.py`, `prompts.py` | Append-only provider session; evidence-driven decisions. |
| §3.2 asynchronous workers, no fixed rounds | `engine.py` queue + tasks | Progress events do not retire a worker. |
| §3.3 worker diagnosis | `models.Diagnosis`, prover prompt | Local/global/uncertain scope, attempts, repair target, witness. |
| §3.4 planner/judge/translator | `engine.worker`, `prompts.py` | Two explicit gates, up to six revisions, scaffold translated by Lean. |
| §3.5 explorers | `Tools(readonly=False)` private copy | Candidates cannot auto-publish; coordinator must submit source. |
| §3.6 falsification | `engine.falsify` | Full root type negated by the harness; helper falsity cannot certify root falsity. |
| §3.7 workspace mutation | `Action`, `Workspace` | ADD_HELPER/RESTATE/REPAIR_PROOF/ABANDON require source; RETRACT mechanical. |
| Appendix E prompts | `prompts/*.md`, `prompts.py` | Adapted, not verbatim; tool names match this harness. |
| Verified code synthesis (Implementer) | Not implemented | Task model has no code mode; fails closed rather than pretending support. |
| Lean MCP / Loogle | `mcp.py` (`LoogleClient`), `loogle_search` tool | Loogle via its public HTTP API, enabled by `[mcp] enabled = true`. Not an MCP server: no Lean MCP package was available, so there is no goal-state or LSP tool. |

## Known limitations

- Root statements must be one `theorem ... := by sorry` with `import`/definitions/hypotheses
  outside the generated region. All 100 FATE-X tasks pass this input validation.
- Generated declarations must be named theorems. Restating a helper is supported; arbitrary
  `def`/`instance`/notation generation is rejected by design.
- `DECOMPOSE_JOINT` commits a coordinator-supplied shared scaffold, then dispatches a prover per
  open goal. There is no dedicated multi-goal planner session.
- A rejected planner after six rounds ends that planner task; the coordinator may retry or
  choose another route. It is not treated as mathematical failure.
- Late worker output is re-elaborated against the current signature and current source. Its
  unrelated source edits are discarded.
- Checkpoint recovery resumes revision state; it does not resume an in-flight provider session.
- `EXPLORE_ALTERNATIVES` dispatches up to `explorer_cohort` explorers tagged with a cohort id and
  journals cohort completion. Comparing candidates and publishing one is left to the coordinator;
  there is no automatic voting or merging.
- `plain`/`naive` baselines share configuration and budgets but are minimal reference modes,
  not reproductions of systems from the paper's baseline table.
