# Sequential Rocq / Choice Trees port — phase 1

Upstream: https://github.com/zhezhouzz/UnifiedInterpreter at
`df70f659d4a7aa7fa75eb27d894388ad8aefc460`.
Public fork: https://github.com/ltzone/UnifiedInterpreter.
Feature branch: `research/ctree-interpreter`. No upstream PR or push.

## Implemented

The function body is a small Rocq program (`Sequential/Syntax.v`), denoted into
CTrees (`Sequential/Denotation.v`). Rocq performs SSA lookup/binding, sequencing,
branch selection, region-local scope, and positive-step `scf.for` iteration using
`CTree.bind` and `CTree.iter`. The OCaml converter does not execute regions or
call `Runner.execute_block` / `Runner.execute_op`. The old backend is selectable
independently with `--backend legacy`; `--backend ctree` never falls back.

The closed operation/attribute subset runs both committed real vector-add
artifacts, including dynamic tail subviews and both branch outcomes. See
[opcode inventory](docs/ctree-operation-inventory.json) for actual static counts.
Supported atoms: integer/float constants; integer add/sub/mul/min/max/div/rem,
comparison and supported casts; tensor.empty; allocation, reinterpretation,
subviews, copy; bufferization live views and destination writes; tensor slices;
HFusion fill/add and HIVM scalar broadcast/add. This is a limited parameter
profile, not general support for every variant of these opcodes.

Existing tensors, descriptors, address spaces, primitive memory computations,
HFusion operators, HIVM operators, and numeric interfaces are reused. ABI inputs
are GM; ordinary allocation retains the legacy ASDefault policy. The frontend
still rejects address-space forms outside its old supported profile.

A semantic `MemoryTransaction` contains an existing finite Free memory
computation, embedded into a CTree and interpreted by the actual memory handler.
Its typed response feeds later SSA/program execution. It is not a RunProgram
callback. Instruction observations are a separate unit-response event whose
output is never available to program evaluation. Memory diagnostic events are
preserved by the embedding theorem; the program driver currently reports
operation locations rather than exporting all primitive memory events.

Views remain descriptors through elaboration and ordinary SSA lookup. Only
semantic tensor reads materialize them. `memref.copy` is synchronous logical
copy with disjointness checks, not an assumed MTE command.

### Failure and commit contract

A memory transaction commits only if the memory handler and its inner result
both succeed. On transaction failure, its partial writes are discarded. Previously completed
operations remain committed; there is no rollback of the entire function.
SSA result-arity validation occurs after a successful transaction commits.
A malformed instruction that allocates but declares no result therefore reports
StaticProgramError while retaining the allocation, matching the old runner's
post-operation result check. This is distinct from transaction rollback.
Numeric/type failures retain the old primitive result semantics. Dynamic errors
are distinct from `Unsupported`, `BudgetExhausted`, and `Deadlock`. No async
scheduler exists; Deadlock is the explicit observation of a stuck tree, not an
implemented hardware deadlock detector. An unrecognized host opcode raises
`Ctree_backend.Unsupported`; the Rocq AUnsupported atom produces Unsupported.

The CTree node budget is cumulative across program IDs. The interpreter returns
remaining fuel; the host launcher passes it to the next invocation. Memory
transactions have a separate fixed 1,000,000-node sub-budget, whose exhaustion
also reports BudgetExhausted without committing.

CTree observation counts and legacy instruction counts differ. Terminators are
PDone; they do not add an operation trace entry. Legacy `primitive_calls` reflects
host ABI handlers only on the CTree path, not the number of extracted operations.
Traces are delivered after each program invocation and cannot influence it.

## Proved

1. For every scalar/result type, finite Free memory computation, initial memory,
   and fuel, the CTree embedding has exactly the original handler's result:

   `run_CTree(fuel, embed(p), m) = run_Free(fuel, p, m)`.

   This includes errors and budget exhaustion, successful memory state, and event
   order. `Sequential/MemoryProof.v: embed_preserves_memory` was developed and
   fully compiled through local Rocq MCP; Print Assumptions returned no axioms.

2. For arbitrary scalar interfaces, environment, memory, shape, type, address
   space and SSA name: if allocation returns descriptor `id` and memory `m′`,
   executing the allocation program commits `m′`, binds that actual `id` to the
   requested name, records the operation location, and preserves lookup at every
   other name. `Sequential/ProgramProof.v: allocate_binds_ssa` was checked and
   fully compiled through local Rocq MCP; Print Assumptions returned no axioms.
   This is an allocation/SSA property of the actual program interpreter, not a
   theorem about all programs or all memory operations.

3. For any atomic operation, if its existing Free memory interpretation succeeds
   and its SSA result binding succeeds, the CTree program interpreter returns
   precisely that environment and committed memory, with its location trace.
   `Sequential/AtomicProof.v: atom_success_correspondence` explicitly uses the
   memory embedding theorem; it is not restricted to allocation.

4. For any atomic operation, an outer Free-handler error or an inner semantic
   error preserves the instruction-entry memory, discarding intermediate writes.
   `atom_failure_rollback` includes budget exhaustion and Unsupported through the
   status mapping. It does not roll back earlier completed instructions.

5. For any atomic operation whose transaction succeeds but SSA binding fails,
   `atom_binding_failure_commits` proves that the error is returned with the
   committed memory. This distinguishes post-commit binding errors from rollback.

All three atomic theorems were fully compiled and checked through local Rocq MCP;
their assumption reports are empty.

These atomic correspondence results share `eval_atom` with the CTree semantics;
that reference is the existing Free handler, not an independently specified MLIR
semantics or the old OCaml runner. Their fixed tree budget of three observations
is sufficient for one atom with PDone; the memory sub-budget is universally
quantified. They do not yet supply composition through arbitrary continuations,
regions or loops.

The proved results are not a conservativity theorem for the whole supported language,
nor an equivalence theorem between the old OCaml runner and the new backend.
Differential tests below are evidence, not a mechanized implementation equivalence.

## Tested

- HFusion and HIVM real VecAdd: n = 0, 1, 255, 256, 257, 512, 513, 777.
  New extracted backend = legacy runner = independent array addition, with exact
  equality on finite dyadic inputs. Program-ID counts and tail-fill branch counts
  also checked. n=0 launches zero bodies, consistent with the existing ABI.
- Nested strided subviews and both `scf.if` directions: output [3,5].
- `scf.for`: zero and four iterations with index induction, plus four with i32 induction, compared with legacy and independent
  expected arrays. The induction variable controls the written subview, so the
  multi-iteration test checks binding and iteration, not repeated identical fills.
- Live alias: a tensor view created before a buffer write sees the new data.
- Explicit unsupported sync, tree budget exhaustion, missing SSA, zero/negative
  loop steps, memory transaction rollback, retention of prior commits, and
  cumulative budget exhaustion across multiple program IDs.
- Post-commit SSA result-arity errors retain allocation identically in the new
  backend and the old runner, tested through their interpreter entry points.
- Existing attention tests were also run; their passing FlashAttention results
  belong to the old runner and do not imply new-backend FlashAttention coverage.

Final validation: `dune build @all`, `dune runtest`, and both explicit real-MLIR
CLI runs at n=777 passed. Each CLI reported maximum error 0. No required VecAdd
size or loop case was skipped.

Initial test-harness issue: host ABI traces were counted as program-body IDs for
n=0. The test now filters the explicit CTree backend trace tag; no execution
semantics was changed to satisfy it.

## Unsupported

- FlashAttention is not ported. Missing HFusion operations: addf/maxnumf,
  linalg transpose/broadcast/matmul/reduce and its combiner region/yield, unary
  exp/log, non-add binary functions, hfusion.cast, tensor expand/collapse shape.
- Missing HIVM operations: vsub/vmul/vdiv, vexp/vln, vreduce, vcast, tensor
  broadcasts (vbrc currently scalar only), matrix/mad protocols and reshape.
- Result-carrying scf.if, loop iter_args/results, nonpositive steps, general CFGs,
  calls, reduction regions and arbitrary multi-block regions.
- Queues, async DMA, pipe flags, Cube/Vector partitioning, sync/barriers, macro
  protocols, and GraphSyncSolver validation. Unknown operations are rejected,
  including in unexecuted branches; sync is never silently ignored.

The actual compiled attention artifacts contain one outer `scf.for`, with i32
bounds and step 20. The loop shape (one induction variable, no iter_args) matches
this port, but the attention body still contains the operations listed above.
The VecAdd artifacts themselves contain no scf.for and are not loop evidence.

## External assumptions and trust boundary

- xDSL 0.74.0 parsing, JSON decoding, host elaboration/type checks, file I/O,
  function ABI initialization and outer program-ID enumeration are unverified.
  The program launcher and multi-core execution are not formalized.
- The existing host float64 numeric backend is reused. It is not NPU bit-accurate
  f16/f32 arithmetic, nor an arithmetic correctness proof. Tests deliberately use
  finite dyadic values for exact model-compatible comparison.
- Extraction and the OCaml compiler/runtime are outside these proofs. Existing
  nat-to-OCaml-int extraction has machine-integer bounds; input guards remain.
  Extracted coinductive CTrees use the standard lazy extraction representation.
- No port source disables guard, positivity, or universe checking; no new admits
  or arbitrary axioms are introduced. This alone is not the trust assessment:
  see the precise upstream dependency boundary below.

### Pinned upstream research dependencies

| Repository | Inspected commit | Role |
|---|---|---|
| vellvm/ctrees | cabcf9bf24b0f459204a7da19ac01b7697ff04e3 | Vendored unmodified CTree.v + Core/*.v only, MIT license retained |
| vellvm/vellvm | 047ffad23dc17b56fb41ea9f7ec0c40fc775261d | Architecture reference; not linked |
| vellvm/micro-vellvm-concurrency | a08a31c9873ae64d44a8b3f75082134f835f7258 | Concurrency reference; not linked |

Vellvm's inspected opam uses Rocq 9.0–9.1, itree 5.2.1–5.2.x, ext-lib 0.13.x,
paco 4.2.3–4.2.x and equations. Micro-vellvm's README instead pins Coq 8.19.1,
itree 5.2.0, coinduction 1.9 and CTrees jfp commit
61428ec4dbc0bb82f91176e54f99bef52f9fd417. It is not an Ascend plugin and is not
assumed compatible with this dependency set. No MLIR-to-LLVM translation is used.

At the inspected CTrees commit, `Interp/FoldStateT.v:1`, `Interp/FoldCTree.v:2`,
`Interp/Internalize.v:1`, `Interp/ITree.v:1,9`, `Interp/Refine.v:1,7,33`,
`Interp/RecursionFacts.v:12`, and `Misc/Head.v:77` disable universe checking.
`Interp/RecursionFacts.v:330,346` are admitted. None of these files is vendored or
imported. We use our own small checked deterministic state interpretation.
The vendored Core/CTreeDefinitions inversion lemmas use JMeq_eq via dependent
destruction; this dependency is disclosed even though the port's headline
proofs do not use them. ITree 5.2.1 also ships optional Axioms.v (guarded_choice)
and Eq/EqAxiom.v (bisimulation_is_eq); these are not required by the port proofs.
The proof-specific assumption reports, not the whole package's marketing claim,
determine what the proved results trust.

## Reproduce

Tested toolchain: OCaml 5.4.1, Rocq core 9.1.0, stdlib 9.0.0, stdpp 1.13.0,
ExtLib 0.13.1, ITree 5.2.1, Paco 4.2.3, Coinduction 1.21,
RelationAlgebra 1.8.0; Python 3.12 and xDSL 0.74.0. CTrees core is checked in.
Proof validation used local rocq-mcp 0.3.1 with pet 0.2.5 via the MCP SDK
stdio transport (not a substitute shell proof loop).

```sh
opam install rocq-core.9.1.0 rocq-stdlib.9.0.0 rocq-stdpp.1.13.0 \
  coq-ext-lib.0.13.1 coq-itree.5.2.1 coq-paco.4.2.3 \
  rocq-coinduction.1.21 rocq-relation-algebra.1.8.0 dune zarith yojson
ATTENTION_PYTHON=python3.12 sh scripts/bootstrap_attention.sh
# Dune copies Rocq sources, builds them and regenerates extraction; no generated
# OCaml semantic file is edited by hand.
sh scripts/check_ctree.sh
# Native source-tree build for MCP/IDE imports:
(cd rocq && rocq makefile -f _CoqProject -o Makefile && make -j4)
# Run with Python from the installed rocq-mcp environment (MCP SDK required):
ROCQ_MCP=/path/to/rocq-mcp /path/to/mcp-python scripts/check_ctree_proofs.py
# Explicit real program invocation:
dune exec kernel-example -- --backend ctree --stage hivm \
  --ir artifacts/kernel_IR/vector-add/hivm.mlir --length 777
```

The backend option is also available on `Vector_add.run` and `Kernel.run` as
`~backend:\`CTree`; their default remains `Legacy` for compatibility.

## Responsibility migration

| Previous OCaml responsibility | New owner | Verification boundary |
|---|---|---|
| Parser.parse, xDSL frontend | unchanged host parser + ctree_backend.compile | unverified |
| Runner.get / result environment update | Rocq lookup / bind_result | program definition + allocation/SSA lemma |
| execute_block sequencing | Rocq denote and CTree.bind | definition accepted, not whole-language equivalence |
| scf.if regions | Rocq denote | branch scope restored; tests |
| scf.for control / induction update | Rocq loop / CTree.iter + existing arithmetic | positive step, overflow check; tests |
| execute_op dispatch | Rocq eval_atom for supported subset | primitives reused; unsupported rejected |
| Memory effect handler | CTree transaction + embedded Free handler | embedding theorem; atomicity tests |
| tensor/view materialization | Rocq read_tensor at read sites | descriptor/liveness tests |
| numeric calculations | existing Rocq primitives + host Numeric.scalar/hivm | host floats outside proof |
| ABI allocation/input/output and launch grid | Vector_add/Kernel host launcher | unverified, sequential enumeration |
| diagnostics / output files | host trace and CLI | observations only |

## Future pipe integration

`seq_effect` separates semantic memory transactions from observations; replace
or extend the semantic signature with architecture-specific requests and provide
new handlers. The existing empty choice signature can be replaced only when a
nondeterministic architecture model is justified. Program denotation need not
be rewritten into a legacy runner callback.

Open questions for the pipe research: request/response types, when writes become
visible, transaction versus enqueue commit boundaries, queue ownership and
capacities, barrier participants and epochs, Cube–Vector communication, failure
and cancellation rules, and how macro protocols map to effects. The sequential
copy here establishes none of these facts. No speculative queue/sync semantics
is added in this phase.
