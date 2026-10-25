import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rmr_baseanddisjoint
open Finset MeasureTheory StatMech StatMech.Walls


/--
[rmr_swapInjection_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_swapInjection_one_eq
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.Walls.rmr_swapInjection_one A B

/--
[rmr_perOrbitCard_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_perOrbitCard_one_eq
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  PerOrbitCard A B := by
-- proof
  apply StatMech.Walls.rmr_perOrbitCard_one A B

/--
[rmr_slabCard_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_slabCard_one_eq
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_slabCard_one A B

/--
[rmr_reimerCardForm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_reimerCardForm_one_eq
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rmr_reimerCardForm_one A B

/--
[rmr_reimer_wprob_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_reimer_wprob_one_eq
  {φ : Fin 1 → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin 1))}
-- given
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.Walls.rmr_reimer_wprob_one φ hφ0 hφ1 A B

/--
[rmr_card_eq_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_card_eq_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hA : StatMech.DependsOn A (↑S))
  (hB : StatMech.DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  #(boxOrbit A B k) = #(imgOrbit A B k) := by
-- proof
  apply StatMech.Walls.rmr_card_eq_of_disjoint_support hA hB hST k

/--
[rmr_slabCard_eq_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_slabCard_eq_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hA : StatMech.DependsOn A (↑S))
  (hB : StatMech.DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  #(poc_slabBox A B k) = #(poc_slabImg A B k) := by
-- proof
  apply StatMech.Walls.rmr_slabCard_eq_of_disjoint_support hA hB hST k

/--
[rmr_slabCard_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_slabCard_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : StatMech.DependsOn A (↑S))
  (hB : StatMech.DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rmr_slabCard_of_disjoint_support hA hB hST

/--
[rmr_reimerCardForm_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_reimerCardForm_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : StatMech.DependsOn A (↑S))
  (hB : StatMech.DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rmr_reimerCardForm_of_disjoint_support hA hB hST

/--
[rmr_reimer_wprob_eq_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_baseanddisjoint.lean)
-/
@[path]
private lemma rmr_reimer_wprob_eq_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
  {S T : Set α}
-- given
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : StatMech.DependsOn A S)
  (hB : StatMech.DependsOn B T)
  (hST : Disjoint S T) :
-- imply
  wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B := by
-- proof
  apply StatMech.Walls.rmr_reimer_wprob_eq_of_disjoint_support φ hφ1 hA hB hST


-- created on 2026-10-23
