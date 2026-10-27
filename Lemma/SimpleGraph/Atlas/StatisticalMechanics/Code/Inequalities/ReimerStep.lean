import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
open Finset StatMech


/--
[mem_boxFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma mem_boxFamily_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {U : Finset α} :
-- imply
  U ∈ boxFamily 𝒜 ℬ ↔ ∃ S ∈ 𝒜, ∃ T ∈ ℬ, Disjoint S T ∧ S ∪ T = U := by
-- proof
  apply StatMech.mem_boxFamily 𝒜 ℬ U

/--
[boxFamily_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_comm_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  boxFamily 𝒜 ℬ = boxFamily ℬ 𝒜 := by
-- proof
  apply StatMech.boxFamily_comm 𝒜 ℬ

/--
[boxFamily_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_mono_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
-- given
  (h𝒜 : 𝒜 ⊆ 𝒜')
  (hℬ : ℬ ⊆ ℬ') :
-- imply
  boxFamily 𝒜 ℬ ⊆ boxFamily 𝒜' ℬ' := by
-- proof
  apply StatMech.boxFamily_mono h𝒜 hℬ

/--
[boxFamily_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  boxFamily ∅ ℬ = ∅ := by
-- proof
  apply StatMech.boxFamily_empty_left ℬ

/--
[boxFamily_empty_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_empty_right_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  boxFamily 𝒜 ∅ = ∅ := by
-- proof
  apply StatMech.boxFamily_empty_right 𝒜

/--
[boxFamily_card_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_card_le_mul_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxFamily 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.boxFamily_card_le_mul 𝒜 ℬ

/--
[boxFamily_filter_notMem_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_filter_notMem_coord_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxFamily 𝒜 ℬ).filter (fun U => i ∉ U) = boxFamily (𝒜.filter (fun S => i ∉ S)) (ℬ.filter (fun T => i ∉ T)) := by
-- proof
  apply StatMech.boxFamily_filter_notMem_coord i 𝒜 ℬ

/--
[downCompressFamily_eq_self_of_isDownAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma downCompressFamily_eq_self_of_isDownAt_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
-- given
  (h : IsDownAtCoord i 𝒜) :
-- imply
  Down.compression i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.downCompressFamily_eq_self_of_isDownAt i h

/--
[boxFamily_downCompress_eq_of_isDownAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma boxFamily_downCompress_eq_of_isDownAt_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsDownAtCoord i 𝒜)
  (hℬ : IsDownAtCoord i ℬ) :
-- imply
  boxFamily (Down.compression i 𝒜) (Down.compression i ℬ) = boxFamily 𝒜 ℬ := by
-- proof
  apply StatMech.boxFamily_downCompress_eq_of_isDownAt i h𝒜 hℬ

/--
[reimerStep_card_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma reimerStep_card_box_eq
  [DecidableEq α] :
-- imply
  (boxFamily reimerStepCexA reimerStepCexB).card = 3 := by
-- proof
  apply StatMech.reimerStep_card_box

/--
[reimerStep_card_box_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma reimerStep_card_box_compressed_eq
  [DecidableEq α] :
-- imply
  (boxFamily (Down.compression 0 reimerStepCexA) (Down.compression 0 reimerStepCexB)).card = 2 := by
-- proof
  apply StatMech.reimerStep_card_box_compressed

/--
[reimerStep_box_compression_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean)
-/
@[path]
private lemma reimerStep_box_compression_false_eq
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), (boxFamily (Down.compression i 𝒜) (Down.compression i ℬ)).card < (boxFamily 𝒜 ℬ).card := by
-- proof
  apply StatMech.reimerStep_box_compression_false


-- created on 2026-10-23
