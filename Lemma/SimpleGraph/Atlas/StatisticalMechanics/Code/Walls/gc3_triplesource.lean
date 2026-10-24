import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc3_triplesource
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc3_sources_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_sources_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n₁ n₂ n₃ : Current V} :
-- imply
  sources G (fun e => n₁ e + n₂ e + n₃ e) = sources G n₁ ∆ sources G n₂ ∆ sources G n₃ := by
-- proof
  apply StatMech.Walls.gc3_sources_add G n₁ n₂ n₃

/--
[gc3_triple_source_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_triple_source_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n₁ n₂ n₃ : Current V}
  {A B C : Finset V}
-- given
  (hA : sources G n₁ = A)
  (hB : sources G n₂ = B)
  (hC : sources G n₃ = C) :
-- imply
  sources G (fun e => n₁ e + n₂ e + n₃ e) = A ∆ B ∆ C := by
-- proof
  apply StatMech.Walls.gc3_triple_source_pinned G n₁ n₂ n₃ hA hB hC

/--
[gc3_mem_triple_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_mem_triple_source_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n₁ n₂ n₃ : Current V}
  {x : V} :
-- imply
  x ∈ sources G (fun e => n₁ e + n₂ e + n₃ e) ↔ ((x ∈ sources G n₁) ≠ (x ∈ sources G n₂)) ≠ (x ∈ sources G n₃) := by
-- proof
  apply StatMech.Walls.gc3_mem_triple_source G n₁ n₂ n₃ x

/--
[gc3_triple_source_self_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_triple_source_self_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n p : Current V} :
-- imply
  sources G (fun e => n e + n e + p e) = sources G p := by
-- proof
  apply StatMech.Walls.gc3_triple_source_self_left G n p

/--
[gc3_boundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_boundary_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ N₃ : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂ ∆ N₃) = StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁ ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂ ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₃ := by
-- proof
  apply StatMech.Walls.gc3_boundary_symmDiff G m N₁ N₂ N₃

/--
[gc3_triple_source_edgecopy_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_triple_source_edgecopy_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ N₃ : Finset (Copy G m)}
  {A B C : Finset V}
-- given
  (hA : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁ = A)
  (hB : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂ = B)
  (hC : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₃ = C) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂ ∆ N₃) = A ∆ B ∆ C := by
-- proof
  apply StatMech.Walls.gc3_triple_source_edgecopy_pinned G m N₁ N₂ N₃ hA hB hC

/--
[gc3_boundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_triplesource.lean)
-/
@[path]
private lemma gc3_boundary_symmDiff_eq_2
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N₁ N₂ N₃ : Finset (Copy G m)} :
-- imply
  StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m (N₁ ∆ N₂ ∆ N₃))) = StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₁)) ∆ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₂)) ∆ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₃)) := by
-- proof
  apply StatMech.Walls.gc3_boundary_symmDiff G m N₁ N₂ N₃


-- created on 2026-10-23
