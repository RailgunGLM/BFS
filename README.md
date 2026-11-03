# Formalising Breadth First Search (BFS) algorithm on simple graph in Lean 4

Imperial College London Department of Mathematics Formalizing Mathematics (MATH60040) Project 1

## Requirements

- Lean 4, managed with `elan`
- Lake, included with Lean 4
- mathlib, fetched by Lake

## Build

From the project directory, run:

```text
lake update
lake build
```

Once mathlib is configured, import it in a Lean file with:

```lean
import Mathlib
```

For faster builds, prefer importing a specific module when possible, such as
`import Mathlib.Data.Tree.Basic`, rather than the entire mathlib library.

The library entry point is [`BFS.lean`](BFS.lean). The implementation is in
[`BFS/BFS.lean`](BFS/BFS.lean), and its correctness proofs are in
[`BFS/BFS_correctness.lean`](BFS/BFS_correctness.lean).