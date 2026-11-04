# Sequential CTree migration

- [x] Build pinned CTrees core and existing semantics.
- [x] Prove finite Free memory embedding preserves handler result (all fuels).
- [x] Define program SSA, operations, regions and positive-step loops in Rocq.
- [x] Prove parameterized SSA/region or SSA/memory program property.
- [x] Extract; execute real HFusion/HIVM VecAdd and loop differential tests.
- [x] Audit assumptions and document boundaries.

Publication target: `ltzone/UnifiedInterpreter`, `research/ctree-interpreter`.
The delivery report records the verified remote commit.

Upstream: df70f659d4a7aa7fa75eb27d894388ad8aefc460.
Proof search/validation uses local rocq-mcp via stdio client, not raw coqc.

Both headline results were fully compiled through MCP and report no axioms:
`embed_preserves_memory` and `allocate_binds_ssa`. The later whole-program milestone below establishes sequential conservativity;
architecture queue/sync interpretations remain future work.

## Follow-up: general atomic instruction correspondence

- [x] Relate every successful atomic instruction's CTree execution to the
  existing Free memory handler and SSA result binding.
- [x] Prove failed memory transactions retain the instruction-entry memory.
- [x] Prove post-commit SSA binding failure retains committed memory.
- [x] Integrate MCP checks and complete read-only review.
  All seven modules compile through MCP; all five theorem assumption reports
  are empty. The post-commit error differential test and build pass.

This atomic milestone was subsequently extended to the whole-program theorem below.

## Whole-program conservativity

- [x] Define independent direct state-transformer reference for all program forms.
- [x] Prove CTree bind and fuel accounting laws.
- [x] Prove bounded direct loops correspond, including failures and zero iterations.
- [x] Prove all programs correspond by structural induction (sequence/regions/loops).
- [x] Check assumptions, extraction regression and independent review.
  All 14 modules pass full MCP compilation; all 13 checked theorem assumptions
  are empty. Complete build/test/real-MLIR CLI checks pass. Publication uses the
  existing fork branch; the delivery report records its verified commit.

Target includes exact status, final memory, operation trace and remaining budget
for every tree/memory budget. The reference shares primitive atom semantics but
does not call the CTree runner. This is not an old-OCaml implementation theorem.

`program_conservativity` and `execute_conservativity` prove exact equality for
all represented programs and both budgets, including status, SSA result, memory,
trace and remaining budget. Both have empty assumption reports. Shared primitive
semantics and the unverified frontend/extraction boundary are in PORT_STATUS.
