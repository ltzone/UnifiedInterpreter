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
`embed_preserves_memory` and `allocate_binds_ssa`. Full-language conservativity
and architecture queue/sync interpretations remain future work.
