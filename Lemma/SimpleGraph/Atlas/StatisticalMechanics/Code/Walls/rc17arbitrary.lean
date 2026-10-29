import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc17arbitrary.Part5
open Finset MeasureTheory StatMech StatMech.Walls


/--
[rc17_deficit_incInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_deficit_incInc_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc17_deficit_incInc hA hB

/--
[rc17_deficit_decDec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_deficit_decDec_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc17_deficit_decDec hA hB

/--
[rc17_deficit_le_zero_of_bothMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_deficit_le_zero_of_bothMonotone_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A ∨ IsDecreasing A)
  (hB : IsIncreasing B ∨ IsDecreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc17_deficit_le_zero_of_bothMonotone hA hB

/--
[rc17_deficitBridge_of_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_deficitBridge_of_nonMonotone_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc17_NonMonotoneDeficit) :
-- imply
  rc7_DeficitBridge := by
-- proof
  apply StatMech.Walls.rc17_deficitBridge_of_nonMonotone h

/--
[rc17_nonMonotone_of_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_nonMonotone_of_deficitBridge_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc7_DeficitBridge) :
-- imply
  rc17_NonMonotoneDeficit := by
-- proof
  apply StatMech.Walls.rc17_nonMonotone_of_deficitBridge h

/--
[rc17_deficitBridge_iff_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_deficitBridge_iff_nonMonotone_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc7_DeficitBridge ↔ rc17_NonMonotoneDeficit := by
-- proof
  apply StatMech.Walls.rc17_deficitBridge_iff_nonMonotone

/--
[rc17_reimerCardFormAll_of_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_reimerCardFormAll_of_nonMonotone_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc17_NonMonotoneDeficit) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc17_reimerCardFormAll_of_nonMonotone h

/--
[rc17_reimerResidue_of_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_reimerResidue_of_nonMonotone_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc17_NonMonotoneDeficit) :
-- imply
  ReimerResidue := by
-- proof
  apply StatMech.Walls.rc17_reimerResidue_of_nonMonotone h

/--
[rc17_reimerWprobCore_of_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_reimerWprobCore_of_nonMonotone_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc17_NonMonotoneDeficit) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc17_reimerWprobCore_of_nonMonotone h

/--
[rc17_reimer_inequality_of_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_reimer_inequality_of_nonMonotone_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc17_NonMonotoneDeficit)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc17_reimer_inequality_of_nonMonotone h hp A B

/--
[rc17_spread_increasing_of_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_spread_increasing_of_increasing_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (rc17_spreadEvent A) := by
-- proof
  apply StatMech.Walls.rc17_spread_increasing_of_increasing hA

/--
[rc17_spread_not_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_spread_not_increasing_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ IsIncreasing (rc17_spreadEvent rbi_A) := by
-- proof
  apply StatMech.Walls.rc17_spread_not_increasing

/--
[rc17_rbiB_not_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_rbiB_not_increasing_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ IsIncreasing rbi_B := by
-- proof
  apply StatMech.Walls.rc17_rbiB_not_increasing

/--
[rc17_rbiB_not_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_rbiB_not_decreasing_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ IsDecreasing rbi_B := by
-- proof
  apply StatMech.Walls.rc17_rbiB_not_decreasing

/--
[rc17_nonMonotone_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_nonMonotone_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ((¬ IsIncreasing rbi_A ∧ ¬ IsDecreasing rbi_A) ∨ (¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B)) ∧ rc5_deficit rbi_A rbi_B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc17_nonMonotone_rbi

/--
[rc17_subset_upClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_subset_upClosure_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A : Set (ConfigSpace (Fin n))} :
-- imply
  A ⊆ rc17_upClosure A := by
-- proof
  apply StatMech.Walls.rc17_subset_upClosure A

/--
[rc17_upClosure_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_upClosure_increasing_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A : Set (ConfigSpace (Fin n))} :
-- imply
  IsIncreasing (rc17_upClosure A) := by
-- proof
  apply StatMech.Walls.rc17_upClosure_increasing A

/--
[rc17_box_subset_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_box_subset_up_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))} :
-- imply
  disjointOccurrence A B ⊆ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B) := by
-- proof
  apply StatMech.Walls.rc17_box_subset_up A B

/--
[rc17_box_le_reflInter_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_box_le_reflInter_up_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))} :
-- imply
  (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ) ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B))) := by
-- proof
  apply StatMech.Walls.rc17_box_le_reflInter_up A B

/--
[rc17_reflInter_subset_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_reflInter_subset_up_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))} :
-- imply
  A ∩ rmr_reflect B ⊆ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B) := by
-- proof
  apply StatMech.Walls.rc17_reflInter_subset_up A B

/--
[rc17_reflInter_card_le_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_reflInter_card_le_up_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))} :
-- imply
  #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ A ∩ rmr_reflect B)) ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B))) := by
-- proof
  apply StatMech.Walls.rc17_reflInter_card_le_up A B

/--
[rc17_functional_bkr_of_reimer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_functional_bkr_of_reimer_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A : ι → Set (ConfigSpace (Fin n))}
  {B : κ → Set (ConfigSpace (Fin n))}
  {K : ι → Set (Fin n)}
  {L : κ → Set (Fin n)}
  {φ : Fin n → Bool → ℝ}
-- given
  (h : ReimerWprobCore)
  (hA : ∀ i, DependsOn (A i) (K i))
  (hB : ∀ j, DependsOn (B j) (L j))
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1) :
-- imply
  wprob φ {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j} ≤ wprob φ (⋃ i, A i) * wprob φ (⋃ j, B j) := by
-- proof
  apply StatMech.Walls.rc17_functional_bkr_of_reimer h A B K L hA hB φ hφ0 hφ1

/--
[rc17_arbitrary_reimer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean)
-/
@[path]
private lemma rc17_arbitrary_reimer_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ {n : ℕ} {A B : Set (ConfigSpace (Fin n))}, (IsIncreasing A ∨ IsDecreasing A) → (IsIncreasing B ∨ IsDecreasing B) → rc5_deficit A B ≤ 0) ∧ (rc7_DeficitBridge ↔ rc17_NonMonotoneDeficit) ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore) ∧ ¬ IsIncreasing (rc17_spreadEvent rbi_A) ∧ (∀ {n : ℕ} (A B : Set (ConfigSpace (Fin n))), (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ) ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B)))) := by
-- proof
  apply StatMech.Walls.rc17_arbitrary_reimer


-- created on 2026-10-23
