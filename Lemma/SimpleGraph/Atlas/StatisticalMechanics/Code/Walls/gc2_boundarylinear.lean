import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc2_boundarylinear
open Finset BigOperators StatMech StatMech.Walls


/--
[gc2_odd_degK_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_odd_degK_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ : Finset (Copy G m)}
  {x : V} :
-- imply
  Odd (RandomCurrent.degK (endsM G m) (N₁ ∆ N₂) x) ↔ (Odd (RandomCurrent.degK (endsM G m) N₁ x) ≠ Odd (RandomCurrent.degK (endsM G m) N₂ x)) := by
-- proof
  apply StatMech.Walls.gc2_odd_degK_symmDiff G m N₁ N₂ x

/--
[gc2_boundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_boundary_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂) = StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁ ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂ := by
-- proof
  apply StatMech.Walls.gc2_boundary_symmDiff G m N₁ N₂

/--
[gc2_mem_boundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_mem_boundary_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ : Finset (Copy G m)}
  {x : V} :
-- imply
  x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂) ↔ ((x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁) ≠ (x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂)) := by
-- proof
  apply StatMech.Walls.gc2_mem_boundary_symmDiff G m N₁ N₂ x

/--
[gc2_boundary_symmDiff_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_boundary_symmDiff_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N ∆ N) = (∅ : Finset V) := by
-- proof
  apply StatMech.Walls.gc2_boundary_symmDiff_self G m N

/--
[gc2_boundary_symmDiff_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_boundary_symmDiff_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m (N₁ ∆ N₂))) = StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₁)) ∆ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₂)) := by
-- proof
  apply StatMech.Walls.gc2_boundary_symmDiff_profile G m N₁ N₂

/--
[gc2_boundary_symmDiff_cancel_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_boundary_symmDiff_cancel_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N P : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N ∆ P) = StatMech.Sharpness.RandomCurrent.sources (endsM G m) N ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) P := by
-- proof
  apply StatMech.Walls.gc2_boundary_symmDiff_cancel_right G m N P

/--
[gc2_boundary_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_boundarylinear.lean)
-/
@[path]
private lemma gc2_boundary_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N P : Finset (Copy G m)}
  {B : Finset V}
-- given
  (hN : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N ∆ P) = B ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) P := by
-- proof
  apply StatMech.Walls.gc2_boundary_surgery G m N P hN


-- created on 2026-10-23
