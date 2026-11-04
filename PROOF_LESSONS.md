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
