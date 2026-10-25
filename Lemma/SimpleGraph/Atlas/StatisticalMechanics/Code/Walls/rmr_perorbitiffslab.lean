import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rmr_perorbitiffslab
open Finset MeasureTheory StatMech StatMech.Walls


/--
[rmr_perOrbitCard_iff_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_perOrbitCard_iff_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  PerOrbitCard A B ↔ poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_perOrbitCard_iff_slabCard A B

/--
[rmr_slabCard_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_slabCard_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : PerOrbitCard A B) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_slabCard_of_perOrbitCard h

/--
[rmr_perOrbitCard_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_perOrbitCard_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  PerOrbitCard A B := by
-- proof
  apply StatMech.Walls.rmr_perOrbitCard_of_slabCard h

/--
[rmr_swapInjection_iff_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_swapInjection_iff_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  r2k_SwapInjection A B ↔ poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_swapInjection_iff_slabCard A B

/--
[rmr_slabCard_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_slabCard_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_SlabCard rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rmr_slabCard_rbi

/--
[rmr_slabCard_of_disjoint_support_po](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_slabCard_of_disjoint_support_po_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_slabCard_of_disjoint_support_po hA hB hST

/--
[rmr_slabCard_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_slabCard_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_slabCard_of_box_empty hbox

/--
[rmr_reimer_wprob_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_perorbitiffslab.lean)
-/
@[path]
private lemma rmr_reimer_wprob_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (h : poc_SlabCard A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.Walls.rmr_reimer_wprob_of_slabCard φ hφ0 hφ1 h


-- created on 2026-10-23
