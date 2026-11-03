/-
Copyright (c) 2026 Git Lun Mak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Git Lun Mak
-/

import Mathlib.Combinatorics.SimpleGraph.Finite

namespace BFS

/-!
# Breadth-first search

This file defines the state and executable implementation of breadth-first
search on a finite simple graph.

The search processes vertices by distance layers. The `seen` field records all
vertices discovered so far, while `frontier` records the layer processed by
the next transition.
-/

/-- The state of a layer-based breadth-first search. -/
structure BFSState (V : Type*) where
  /-- Vertices in the layer currently being processed. -/
  frontier : Finset V
  /-- All vertices discovered so far, including the current frontier. -/
  seen : Finset V
  /-- Assigned distance from the root; `none` means undiscovered. -/
  distance : V → Option Nat
  /-- Distance of vertices in the current frontier from the root. -/
  depth : Nat

/-- Construct the initial BFS state, with `root` as the sole vertex in layer 0. -/
def initialState {V : Type*} [DecidableEq V] (root : V) : BFSState V where
  frontier := {root}
  seen := {root}
  distance := fun v => if v = root then some 0 else none
  depth := 0

/--
Compute the next frontier by collecting all neighbours of the current frontier
and removing vertices that have already been discovered.
-/
def nextFrontier {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (frontier seen : Finset V) : Finset V :=
  (frontier.biUnion fun u => G.neighborFinset u) \ seen

/--
Process one BFS layer, assigning the next distance to newly discovered
vertices.
-/
def bfsStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (state : BFSState V) : BFSState V :=
  let newFrontier := nextFrontier G state.frontier state.seen
  {
    frontier := newFrontier
    seen := state.seen ∪ newFrontier
    distance := fun v => if v ∈ newFrontier then some (state.depth + 1) else state.distance v
    depth := state.depth + 1
  }

/--
Run at most `fuel` BFS transitions, stopping early if the frontier is empty.

This bounded recursion makes termination evident to Lean. The choice of fuel
used by `bfs` below should be justified alongside the BFS invariants.
-/
def bfsAux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat → BFSState V → BFSState V
  | 0, state => state
  | fuel + 1, state =>
      if state.frontier = ∅ then
        state
      else
        bfsAux G fuel (bfsStep G state)

/--
Run the layer-based BFS from `root`.
-/
def bfs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) : BFSState V :=
  bfsAux G (Fintype.card V) (initialState root)

end BFS
