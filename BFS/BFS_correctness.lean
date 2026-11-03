/-
Copyright (c) 2026 Git Lun Mak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Git Lun Mak
-/

import BFS.BFS
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace BFS

/-!
# Correctness of breadth-first search

This file proves that the layer-based breadth-first search implementation
discovers exactly the vertices reachable from its root and assigns each such
vertex its graph distance.

The main results are `bfs_reachable_mem_seen`, `bfs_distance_correct` and
`bfs_unreachable_none`.
-/

variable {V : Type*}
variable (G : SimpleGraph V)

/--
The invariant records that `seen` contains precisely the reachable vertices
within the processed distance range, `frontier` is the current distance layer,
and every assigned distance agrees with the graph distance.

The reachability hypotheses are essential because `SimpleGraph.dist` uses `0`
as its junk value for pairs of vertices that are not reachable.
-/
structure BFSInvariant {V : Type*}
    (G : SimpleGraph V) (root : V) (state : BFSState V) : Prop where
  /-- The vertices seen so far are exactly those within the current depth. -/
  seen_iff : ∀ v, v ∈ state.seen ↔
    G.Reachable root v ∧ G.dist root v ≤ state.depth
  /-- The frontier is exactly the current distance layer. -/
  frontier_iff : ∀ v, v ∈ state.frontier ↔
    G.Reachable root v ∧ G.dist root v = state.depth
  /-- Every assigned distance agrees with the graph distance. -/
  distance_iff : ∀ (v : V) (d : Nat),
    state.distance v = some d ↔
      v ∈ state.seen ∧ G.dist root v = d

/-- Every distance up to a reachable vertex's distance occurs on a shortest path. -/
lemma exists_reachable_at_dist (root w : V) (n : Nat)
    (hw : G.Reachable root w) (hn : n ≤ G.dist root w) :
    ∃ u, G.Reachable root u ∧ G.dist root u = n := by
  obtain ⟨p, hp⟩ := hw.exists_walk_length_eq_dist
  let u := p.getVert n
  have hPrefix : G.dist root u ≤ n := by
    have hWalk := G.dist_le (p.take n)
    rw [p.take_length] at hWalk
    simp at hWalk
    exact hWalk.left
  have hSuffix : G.dist u w ≤ G.dist root w - n := by
    have hWalk := G.dist_le (p.drop n)
    rw [p.drop_length, hp] at hWalk
    simpa [u] using hWalk
  have hLower : n ≤ G.dist root u := by
    have hTriangle' := (p.drop n).reachable.dist_triangle_right root
    have hTriangle : G.dist root w ≤ G.dist root u + G.dist u w := by
      simpa [u] using hTriangle'
    omega
  exact ⟨u, (p.take n).reachable, le_antisymm hPrefix hLower⟩

/-- A vertex at the next distance has an adjacent predecessor at the current distance. -/
lemma exists_adj_eq_dist_of_dist_eq_succ (root v : V) (state : BFSState V)
    (hReach : G.Reachable root v)
    (hDist : G.dist root v = state.depth + 1) :
    ∃ u, G.Adj u v ∧ G.dist root u = state.depth := by
  obtain ⟨p, hp⟩ := hReach.exists_walk_length_eq_dist
  have hpLen : p.length = state.depth + 1 := by
    rw [hp, hDist]
  have hpNotNil : ¬p.Nil := by
    intro hNil
    have hpZero : p.length = 0 := hNil.length_eq_zero
    omega
  have hAdj := SimpleGraph.Walk.adj_penultimate hpNotNil
  refine ⟨p.penultimate, hAdj, ?_⟩
  have hUpper : G.dist root p.penultimate ≤ state.depth := by
    have hWalk := G.dist_le p.dropLast
    rw [p.length_dropLast, hpLen] at hWalk
    omega
  have hLower : state.depth ≤ G.dist root p.penultimate := by
    have hTriangle := (p.dropLast.reachable).dist_triangle_left v
    rw [hDist, SimpleGraph.dist_eq_one_iff_adj.mpr hAdj] at hTriangle
    omega
  omega

variable [DecidableEq V]

/-- The initial BFS state satisfies the invariant. -/
theorem initialState_invariant (root : V) :
    BFSInvariant G root (initialState root) := by
  have hRoot (v : V) :
      v ∈ ({root} : Finset V) ↔
        G.Reachable root v ∧ G.dist root v = 0 := by
    simp only [Finset.mem_singleton,
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
    constructor
    · intro hv
      subst v
      exact ⟨SimpleGraph.Reachable.refl root, Or.inl rfl⟩
    · rintro ⟨hReach, hEq | hNotReach⟩
      · exact hEq.symm
      · exact (hNotReach hReach).elim
  refine { seen_iff := ?_, frontier_iff := ?_, distance_iff := ?_ }
  · intro v
    change v ∈ ({root} : Finset V) ↔
      G.Reachable root v ∧ G.dist root v ≤ 0
    simpa only [nonpos_iff_eq_zero] using hRoot v
  · intro v
    change v ∈ ({root} : Finset V) ↔
      G.Reachable root v ∧ G.dist root v = 0
    exact hRoot v
  · unfold initialState
    intro v d
    simp only [Option.ite_none_right_eq_some, Option.some.injEq, Finset.mem_singleton,
      and_congr_right_iff]
    intro hv
    apply Eq.congr
    rw [hv]
    exact Eq.symm SimpleGraph.dist_self
    rfl

variable [Fintype V] [DecidableRel G.Adj]

/-- The next frontier consists exactly of reachable vertices at the next distance. -/
lemma nextFrontier_iff (root : V) (state : BFSState V)
    (hInv : BFSInvariant G root state) (v : V) :
    v ∈ nextFrontier G state.frontier state.seen ↔
      G.Reachable root v ∧ G.dist root v = state.depth + 1 := by
  simp only [nextFrontier, Finset.mem_sdiff, Finset.mem_biUnion,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨u, hu, huv⟩, hNotSeen⟩
    have ⟨huReach, huDist⟩ := (hInv.frontier_iff u).mp hu
    have hDist := huReach.dist_triangle_left v
    rw [huDist, SimpleGraph.dist_eq_one_iff_adj.mpr huv] at hDist
    refine ⟨huReach.trans huv.reachable, ?_⟩
    have hNotLe : ¬G.dist root v ≤ state.depth := by
      intro hLe
      exact hNotSeen ((hInv.seen_iff v).mpr ⟨huReach.trans huv.reachable, hLe⟩)
    omega
  · rintro ⟨hReach, hDist⟩
    by_cases hSeen : v ∈ state.seen
    · have hLe := (hInv.seen_iff v).mp hSeen |>.right
      omega
    · obtain ⟨u, huvAdj, huDist⟩ :=
        exists_adj_eq_dist_of_dist_eq_succ G root v state hReach hDist
      exact ⟨⟨u, (hInv.frontier_iff u).mpr ⟨
        hReach.trans huvAdj.reachable.symm, huDist⟩, huvAdj⟩, hSeen⟩

/-- The seen vertices after one step are exactly those within the new depth. -/
lemma bfsStep_seen_iff (root : V) (state : BFSState V)
    (hInv : BFSInvariant G root state) (v : V) :
    v ∈ (bfsStep G state).seen ↔
      G.Reachable root v ∧ G.dist root v ≤ state.depth + 1 := by
  change v ∈ state.seen ∪ nextFrontier G state.frontier state.seen ↔ _
  rw [Finset.mem_union]
  constructor
  · rintro (hSeen | hNew)
    · exact (hInv.seen_iff v).mp hSeen |>.imp_right (by omega)
    · exact (nextFrontier_iff G root state hInv v).mp hNew |>.imp_right (by omega)
  · rintro ⟨hReach, hDist⟩
    by_cases hSeen : v ∈ state.seen
    · exact Or.inl hSeen
    · right
      apply (nextFrontier_iff G root state hInv v).mpr
      refine ⟨hReach, ?_⟩
      have hNotLe : ¬G.dist root v ≤ state.depth := by
        intro hLe
        exact hSeen ((hInv.seen_iff v).mpr ⟨hReach, hLe⟩)
      omega

/-- One BFS transition preserves the invariant. -/
theorem bfsStep_preserves_invariant (root : V) (state : BFSState V)
    (hInv : BFSInvariant G root state) :
    BFSInvariant G root (bfsStep G state) := by
  let nf := nextFrontier G state.frontier state.seen
  have hNew (v : V) :
      v ∈ nf ↔ G.Reachable root v ∧ G.dist root v = state.depth + 1 := by
    simpa [nf] using nextFrontier_iff G root state hInv v
  refine { seen_iff := ?_, frontier_iff := ?_, distance_iff := ?_ }
  · intro v
    exact bfsStep_seen_iff G root state hInv v
  · intro v
    change v ∈ nf ↔ G.Reachable root v ∧ G.dist root v = state.depth + 1
    exact hNew v
  · intro v d
    change (if v ∈ nf then some (state.depth + 1) else state.distance v) = some d ↔
      v ∈ state.seen ∪ nf ∧ G.dist root v = d
    by_cases hNewMem : v ∈ nf
    · rw [ite_eq_left hNewMem]
      constructor
      · intro h
        have hd : state.depth + 1 = d := Option.some.inj h
        exact ⟨Finset.mem_union.mpr (Or.inr hNewMem),
          (hNew v).mp hNewMem |>.right ▸ hd⟩
      · rintro ⟨_, hd⟩
        have hExact := (hNew v).mp hNewMem |>.right
        exact congrArg some (hExact.symm.trans hd)
    · rw [ite_eq_right hNewMem, hInv.distance_iff]
      simp [hNewMem]

/-- Any bounded number of BFS transitions preserves the invariant. -/
theorem bfsAux_preserves_invariant (root : V) (fuel : Nat)
    (state : BFSState V)
    (hInv : BFSInvariant G root state) :
    BFSInvariant G root (bfsAux G fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simpa [bfsAux] using hInv
  | succ fuel ih =>
      by_cases hEmpty : state.frontier = ∅
      · simpa [bfsAux, hEmpty] using hInv
      · simp only [bfsAux, hEmpty]
        exact ih (bfsStep G state) (bfsStep_preserves_invariant G root state hInv)

/-- The state returned by `bfs` satisfies the invariant. -/
theorem bfs_invariant (root : V) :
    BFSInvariant G root (bfs G root) := by
  unfold bfs
  exact bfsAux_preserves_invariant G root (Fintype.card V)
    (initialState root) (initialState_invariant G root)

/-- The depth increases by one for every transition before an empty frontier. -/
lemma bfsAux_depth_of_frontier_nonempty (fuel : Nat) (state : BFSState V)
    (hFrontier : (bfsAux G fuel state).frontier ≠ ∅) :
    (bfsAux G fuel state).depth = state.depth + fuel := by
  induction fuel generalizing state with
  | zero =>
      simp [bfsAux]
  | succ fuel ih =>
      by_cases hEmpty : state.frontier = ∅
      · simp [bfsAux, hEmpty] at hFrontier
      · simp only [bfsAux, hEmpty, ↓reduceIte] at hFrontier ⊢
        have hIH := ih (bfsStep G state) hFrontier
        calc
          (bfsAux G fuel (bfsStep G state)).depth =
              (bfsStep G state).depth + fuel := hIH
          _ = state.depth + (fuel + 1) := by
            simp [bfsStep]
            omega

/-- The final BFS frontier is empty after processing `Fintype.card V` layers. -/
lemma bfs_frontier_empty (root : V) :
    (bfs G root).frontier = ∅ := by
  have hInv := bfs_invariant G root
  by_contra hNotEmpty
  unfold bfs at hNotEmpty
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hNotEmpty
  have hDepthFinal :
      (bfs G root).depth = Fintype.card V := by
    unfold bfs
    simpa [initialState] using
      bfsAux_depth_of_frontier_nonempty G (Fintype.card V) (initialState root)
        (by simpa using hNotEmpty)
  have hwReachDist := (hInv.frontier_iff w).mp hw
  obtain ⟨p, hp⟩ := hwReachDist.left.exists_walk_length_eq_dist
  have hpPath := p.isPath_of_length_eq_dist hp
  have hpLt := hpPath.length_lt
  rw [← hDepthFinal, ← hwReachDist.right, hp] at hpLt
  omega

/--
Every reachable vertex is discovered by the final BFS state.

The proof uses the finite fuel bound. A shortest path is a simple path and
therefore has length strictly less than `Fintype.card V`. If the final
frontier were nonempty after all fuel had been consumed, its depth would be
`Fintype.card V`, contradicting that same bound. Otherwise, every reachable
distance layer is represented by the invariant, so the target vertex is seen.
-/
theorem bfs_reachable_mem_seen (root v : V)
    (hReach : G.Reachable root v) :
    v ∈ (bfs G root).seen := by
  have hInv := bfs_invariant G root
  have hFrontierEmpty := bfs_frontier_empty G root
  by_contra hNotSeen'
  have hNotLe : ¬G.dist root v ≤ (bfs G root).depth := by
    intro hLe
    exact hNotSeen' ((hInv.seen_iff v).mpr ⟨hReach, hLe⟩)
  obtain ⟨u, huReach, huDist⟩ :=
    exists_reachable_at_dist G root v (bfs G root).depth hReach (by omega)
  simpa [hFrontierEmpty] using (hInv.frontier_iff u).mpr ⟨huReach, huDist⟩

/-- The final BFS distance agrees with graph distance for reachable vertices. -/
theorem bfs_distance_correct (root v : V)
    (hReach : G.Reachable root v) :
    (bfs G root).distance v = some (G.dist root v) := by
  have hInv := bfs_invariant G root
  have hSeen := bfs_reachable_mem_seen G root v hReach
  exact (hInv.distance_iff v (G.dist root v)).mpr ⟨hSeen, rfl⟩

/-- An unreachable vertex remains undiscovered. -/
theorem bfs_unreachable_none (root v : V)
    (hNotReach : ¬ G.Reachable root v) :
    (bfs G root).distance v = none := by
  have hInv := bfs_invariant G root
  have hNotSeen : v ∉ (bfs G root).seen := by
    intro hSeen
    exact hNotReach ((hInv.seen_iff v).mp hSeen).left
  by_contra hNe
  cases hDist : (bfs G root).distance v with
  | none => exact hNe hDist
  | some d =>
      exact hNotSeen ((hInv.distance_iff v d).mp hDist).left

end BFS
