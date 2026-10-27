import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
open Finset MeasureTheory StatMech StatMech.Walls


/--
[rc8_half_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_half_le_one_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc8_half : ℝ≥0) ≤ 1 := by
-- proof
  apply StatMech.Walls.rc8_half_le_one

/--
[rc8_half_singleton_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_half_singleton_bool_eq
  [Fintype α]
  [DecidableEq α]
  {b : Bool} :
-- imply
  (bernoulliMeasure rc8_half rc8_half_le_one).real {b} = (1 / 2 : ℝ) := by
-- proof
  apply StatMech.Walls.rc8_half_singleton_bool b

/--
[rc8_half_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_half_singleton_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real {ω} = (1 / 2) ^ (Fintype.card α) := by
-- proof
  apply StatMech.Walls.rc8_half_singleton ω

/--
[rc8_card_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_card_bridge_eq
  [Fintype α]
  [DecidableEq α]
  {S : Set (ConfigSpace α)} :
-- imply
  (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real S = (#(univ.filter (fun ω => ω ∈ S)) : ℝ) * (1 / 2) ^ (Fintype.card α) := by
-- proof
  apply StatMech.Walls.rc8_card_bridge S

/--
[rc8_antiHarris](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_antiHarris_eq
  [Fintype α]
  [DecidableEq α]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace α)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  (bernoulliProductMeasure (E := α) p hp).real (A ∩ B) ≤ (bernoulliProductMeasure (E := α) p hp).real A * (bernoulliProductMeasure (E := α) p hp).real B := by
-- proof
  apply StatMech.Walls.rc8_antiHarris hp hA hB

/--
[rc8_antiHarris'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_antiHarris'_eq
  [Fintype α]
  [DecidableEq α]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace α)}
-- given
  (hp : p ≤ 1)
  (hA : IsDecreasing A)
  (hB : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := α) p hp).real (A ∩ B) ≤ (bernoulliProductMeasure (E := α) p hp).real A * (bernoulliProductMeasure (E := α) p hp).real B := by
-- proof
  apply StatMech.Walls.rc8_antiHarris' hp hA hB

/--
[rc8_harrisDec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_harrisDec_eq
  [Fintype α]
  [DecidableEq α]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace α)}
-- given
  (hp : p ≤ 1)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  (bernoulliProductMeasure (E := α) p hp).real A * (bernoulliProductMeasure (E := α) p hp).real B ≤ (bernoulliProductMeasure (E := α) p hp).real (A ∩ B) := by
-- proof
  apply StatMech.Walls.rc8_harrisDec hp hA hB

/--
[rc8_isDecreasing_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_isDecreasing_reflect_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsDecreasing (rmr_reflect A) := by
-- proof
  apply StatMech.Walls.rc8_isDecreasing_reflect hA

/--
[rc8_reflect_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_reflect_prob_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real (rmr_reflect B) = (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real B := by
-- proof
  apply StatMech.Walls.rc8_reflect_prob B

/--
[rc8_cardForm_inc_dec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_cardForm_inc_dec_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  #(univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤ #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc8_cardForm_inc_dec hA hB

/--
[rc8_cardForm_dec_inc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_cardForm_dec_inc_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsDecreasing A)
  (hB : IsIncreasing B) :
-- imply
  #(univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤ #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc8_cardForm_dec_inc hA hB

/--
[rc8_deficit_le_zero_inc_dec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_deficit_le_zero_inc_dec_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc8_deficit_le_zero_inc_dec hA hB

/--
[rc8_deficit_le_zero_dec_inc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_deficit_le_zero_dec_inc_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsDecreasing A)
  (hB : IsIncreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc8_deficit_le_zero_dec_inc hA hB

/--
[rc8_reimerCardForm_inc_dec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_reimerCardForm_inc_dec_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  StatMech.poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc8_reimerCardForm_inc_dec hA hB

/--
[rc8_reimerCardForm_dec_inc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_reimerCardForm_dec_inc_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsDecreasing A)
  (hB : IsIncreasing B) :
-- imply
  StatMech.poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc8_reimerCardForm_dec_inc hA hB

/--
[rc8_deficitBridge_iff_nonOpp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_deficitBridge_iff_nonOpp_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc7_DeficitBridge ↔ rc8_DeficitBridgeNonOpp := by
-- proof
  apply StatMech.Walls.rc8_deficitBridge_iff_nonOpp

/--
[rc8_reimerCardFormAll_of_nonOpp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_reimerCardFormAll_of_nonOpp_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc8_DeficitBridgeNonOpp) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc8_reimerCardFormAll_of_nonOpp h

/--
[rc8_deficit_univ_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_deficit_univ_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_deficit (Set.univ : Set (ConfigSpace α)) Set.univ ≤ 0 := by
-- proof
  apply StatMech.Walls.rc8_deficit_univ_univ

/--
[rc8_cardform_oppositeMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean)
-/
@[path]
private lemma rc8_cardform_oppositeMonotone_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ {A B : Set (ConfigSpace α)}, IsIncreasing A → IsDecreasing B → rc5_deficit A B ≤ 0) ∧ (∀ {A B : Set (ConfigSpace α)}, IsDecreasing A → IsIncreasing B → rc5_deficit A B ≤ 0) ∧ (rc7_DeficitBridge ↔ rc8_DeficitBridgeNonOpp) ∧ (rc8_DeficitBridgeNonOpp → ReimerCardFormAll) := by
-- proof
  apply StatMech.Walls.rc8_cardform_oppositeMonotone


-- created on 2026-10-23
