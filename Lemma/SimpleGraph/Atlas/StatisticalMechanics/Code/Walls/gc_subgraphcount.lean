import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc_subgraphcount
open Finset BigOperators StatMech StatMech.Walls


/--
[gc_binom_eq_subgraph_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_subgraphcount.lean)
-/
@[path]
private lemma gc_binom_eq_subgraph_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m n : ↥G.edgeFinset → ℕ} :
-- imply
  #((univ : Finset (Finset (Copy G m))).filter (fun N => profileFlux G m N = n)) = ∏ e : ↥G.edgeFinset, (m e).choose (n e) := by
-- proof
  apply StatMech.Walls.gc_binom_eq_subgraph_count G m n

/--
[gc_boundary_iff_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_subgraphcount.lean)
-/
@[path]
private lemma gc_boundary_iff_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {B : Finset V}
  {N : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B ↔ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N)) = B := by
-- proof
  apply StatMech.Walls.gc_boundary_iff_profile G m B N

/--
[gc_subgraph_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_subgraphcount.lean)
-/
@[path]
private lemma gc_subgraph_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {B : Finset V} :
-- imply
  (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0)) = #((univ : Finset (Finset (Copy G m))).filter (fun N => StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B)) := by
-- proof
  apply StatMech.Walls.gc_subgraph_count G m B

/--
[gc_subgraph_count_eq_sum_over_profiles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_subgraphcount.lean)
-/
@[path]
private lemma gc_subgraph_count_eq_sum_over_profiles_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {B : Finset V} :
-- imply
  #((univ : Finset (Finset (Copy G m))).filter (fun N => StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B)) = ∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0) := by
-- proof
  apply StatMech.Walls.gc_subgraph_count_eq_sum_over_profiles G m B


-- created on 2026-10-23
