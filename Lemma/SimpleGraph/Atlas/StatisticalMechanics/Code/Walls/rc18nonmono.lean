import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
open Finset StatMech StatMech.Walls


/--
[rc18_card_box_eq_cylBoxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_card_box_eq_cylBoxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) = #(rc18_cylBoxSupp A B) := by
-- proof
  apply StatMech.Walls.rc18_card_box_eq_cylBoxSupp A B

/--
[rc18_deficit_of_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_deficit_of_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (h : rc18_CylBoxReflInter) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc18_deficit_of_cylBoxReflInter h A B

/--
[rc18_nonMonotone_of_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_nonMonotone_of_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc18_CylBoxReflInter) :
-- imply
  rc17_NonMonotoneDeficit := by
-- proof
  apply StatMech.Walls.rc18_nonMonotone_of_cylBoxReflInter h

/--
[rc18_cylBoxReflInter_of_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_cylBoxReflInter_of_deficitBridge_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc7_DeficitBridge) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc18_cylBoxReflInter_of_deficitBridge h

/--
[rc18_deficitBridge_iff_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_deficitBridge_iff_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc7_DeficitBridge ↔ rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc18_deficitBridge_iff_cylBoxReflInter

/--
[rc18_cylBoxReflInter_iff_nonMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_cylBoxReflInter_iff_nonMonotone_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit := by
-- proof
  apply StatMech.Walls.rc18_cylBoxReflInter_iff_nonMonotone

/--
[rc18_reimerWprobCore_of_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_reimerWprobCore_of_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc18_CylBoxReflInter) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc18_reimerWprobCore_of_cylBoxReflInter h

/--
[rc18_reimer_inequality_of_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_reimer_inequality_of_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc18_CylBoxReflInter)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc18_reimer_inequality_of_cylBoxReflInter h hp A B

/--
[rc18_cylBoxSupp_subset_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_cylBoxSupp_subset_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc18_cylBoxSupp A B ⊆ rc10_boxSupp (eventFamily A) (eventFamily B) := by
-- proof
  apply StatMech.Walls.rc18_cylBoxSupp_subset_boxSupp A B

/--
[rc18_card_cylBoxSupp_le_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_card_cylBoxSupp_le_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(rc18_cylBoxSupp A B) ≤ #(rc10_boxSupp (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc18_card_cylBoxSupp_le_boxSupp A B

/--
[rc18_card_box_le_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_card_box_le_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(rc10_boxSupp (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc18_card_box_le_boxSupp A B

/--
[rc18_familyBKR_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_familyBKR_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc18_familyBKR_false

/--
[rc18_cylBoxReflInter_of_bkr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_cylBoxReflInter_of_bkr_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc18_cylBoxReflInter_of_bkr hA hB

/--
[rc18_cylBoxReflInter_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_cylBoxReflInter_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ((¬ IsIncreasing rbi_A ∧ ¬ IsDecreasing rbi_A) ∨ (¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B)) ∧ #(rc18_cylBoxSupp rbi_A rbi_B) ≤ #(rc10_reflInter (eventFamily rbi_A) (eventFamily rbi_B)) := by
-- proof
  apply StatMech.Walls.rc18_cylBoxReflInter_rbi

/--
[rc18_nonmono_reimer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean)
-/
@[path]
private lemma rc18_nonmono_reimer_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit) ∧ (rc18_CylBoxReflInter → ReimerWprobCore) ∧ (∀ (A B : Set (ConfigSpace α)), #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(rc10_boxSupp (eventFamily A) (eventFamily B))) ∧ ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc18_nonmono_reimer


-- created on 2026-10-23
