# Sequential CTree proof lessons

- For an atomic instruction, two visible events (location observation and memory
  transaction) and one return observation suffice. This tree budget is separate
  from the universally quantified Free-memory budget. It cannot be reused as a
  general bound for loops or arbitrary continuations.
- Reduce only the outer program interpreter first, then rewrite
  `embed_preserves_memory`. Keep the arbitrary `eval_atom env op` opaque in the
  proof argument rather than splitting every opcode. This exposes the original
  Free-handler equation and makes transaction success/error cases reusable.
- There are two commit boundaries: an inner/outer transaction error discards
  intermediate memory, whereas SSA binding happens after transaction commit.
  A result-arity error therefore retains committed memory. Do not state a blanket
  "all instruction errors roll back" theorem.

- For error-aware bind, separately running a successful sub-tree spends a return
  observation that bind eliminates. The direct reference restores one unit before
  running its continuation. Loop continuation consumes that unit as a Guard, so
  it instead recurs at the body's returned budget.
- State-transformer extensionality can remain pointwise: prove runner bind
  associativity and continuation congruence by fuel induction. Do not introduce
  functional extensionality or a coinductive tree equality axiom just to rewrite
  nested binds.
- A bounded reference loop needs a fuel-monotone body. A generic reference
  computation can fabricate remaining fuel; pointwise correspondence to the
  actual runner supplies the required remaining-budget bound.
