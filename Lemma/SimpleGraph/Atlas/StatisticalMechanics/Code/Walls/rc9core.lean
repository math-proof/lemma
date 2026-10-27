import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
open Finset StatMech StatMech.Walls


/--
[rc9_flipCfg_eq_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_flipCfg_eq_compl_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  flipCfg ω = rmr_compl ω := by
-- proof
  apply StatMech.Walls.rc9_flipCfg_eq_compl ω

/--
[rc9_flip_preimage_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_flip_preimage_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)} :
-- imply
  flipCfg ⁻¹' (flipCfg ⁻¹' A) = A := by
-- proof
  apply StatMech.Walls.rc9_flip_preimage_involutive A

/--
[rc9_isDecreasing_flip_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_isDecreasing_flip_preimage_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsDecreasing (flipCfg ⁻¹' A) := by
-- proof
  apply StatMech.Walls.rc9_isDecreasing_flip_preimage hA

/--
[rc9_card_flip_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_card_flip_eq_eq
  [Fintype α]
  [DecidableEq α]
  {S' S : Set (ConfigSpace α)}
  [DecidablePred (· ∈ S')]
  [DecidablePred (· ∈ S)]
-- given
  (h : ∀ ω, ω ∈ S' ↔ flipCfg ω ∈ S) :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ S')) = #(univ.filter (fun ω : ConfigSpace α => ω ∈ S)) := by
-- proof
  apply StatMech.Walls.rc9_card_flip_eq h

/--
[rc9_rhs_flip_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_rhs_flip_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ (flipCfg ⁻¹' A) ∩ rmr_reflect (flipCfg ⁻¹' B) ↔ flipCfg ω ∈ A ∩ rmr_reflect B := by
-- proof
  apply StatMech.Walls.rc9_rhs_flip_iff A B ω

/--
[rc9_box_flip_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_box_flip_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ disjointOccurrence (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) ↔ flipCfg ω ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.Walls.rc9_box_flip_iff A B ω

/--
[rc9_deficit_flip_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_flip_invariant_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) = rc5_deficit A B := by
-- proof
  apply StatMech.Walls.rc9_deficit_flip_invariant A B

/--
[rc9_deficit_le_of_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_le_of_flip_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) ≤ 0) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc9_deficit_le_of_flip h

/--
[rc9_card_compl_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_card_compl_swap_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ B ∩ rmr_reflect A)) = #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc9_card_compl_swap A B

/--
[rc9_deficit_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_swap_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc5_deficit A B = rc5_deficit B A := by
-- proof
  apply StatMech.Walls.rc9_deficit_swap A B

/--
[rc9_deficit_le_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_le_swap_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : rc5_deficit A B ≤ 0) :
-- imply
  rc5_deficit B A ≤ 0 := by
-- proof
  apply StatMech.Walls.rc9_deficit_le_swap h

/--
[rc9_decDec_of_incInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_decDec_of_incInc_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hII : ∀ {A B : Set (ConfigSpace α)}, IsIncreasing A → IsIncreasing B → rc5_deficit A B ≤ 0)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc9_decDec_of_incInc hII hA hB

/--
[rc9_deficitBridge_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficitBridge_of_residue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc9_DeficitBridgeResidue) :
-- imply
  rc7_DeficitBridge := by
-- proof
  apply StatMech.Walls.rc9_deficitBridge_of_residue h

/--
[rc9_residue_of_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_residue_of_deficitBridge_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc7_DeficitBridge) :
-- imply
  rc9_DeficitBridgeResidue := by
-- proof
  apply StatMech.Walls.rc9_residue_of_deficitBridge h

/--
[rc9_residue_iff_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_residue_iff_deficitBridge_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc7_DeficitBridge ↔ rc9_DeficitBridgeResidue := by
-- proof
  apply StatMech.Walls.rc9_residue_iff_deficitBridge

/--
[rc9_residue_iff_nonOpp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_residue_iff_nonOpp_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc9_DeficitBridgeResidue ↔ rc8_DeficitBridgeNonOpp := by
-- proof
  apply StatMech.Walls.rc9_residue_iff_nonOpp

/--
[rc9_reimerCardFormAll_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_reimerCardFormAll_of_residue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc9_DeficitBridgeResidue) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc9_reimerCardFormAll_of_residue h

/--
[rc9_deficit_swap_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_swap_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_deficit rbi_A rbi_B = rc5_deficit rbi_B rbi_A := by
-- proof
  apply StatMech.Walls.rc9_deficit_swap_rbi

/--
[rc9_deficit_flip_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_flip_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_deficit (flipCfg ⁻¹' rbi_A) (flipCfg ⁻¹' rbi_B) = rc5_deficit rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc9_deficit_flip_rbi

/--
[rc9_deficit_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc9_deficit_one A B

/--
[rc9_deficit_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_deficit_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_deficit rbi_A rbi_B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc9_deficit_rbi

/--
[rc9_cardform_symmetry_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc9core.lean)
-/
@[path]
private lemma rc9_cardform_symmetry_reduction_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ A B : Set (ConfigSpace α), rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) = rc5_deficit A B) ∧ (∀ A B : Set (ConfigSpace α), rc5_deficit A B = rc5_deficit B A) ∧ (rc7_DeficitBridge ↔ rc9_DeficitBridgeResidue) ∧ (rc9_DeficitBridgeResidue ↔ rc8_DeficitBridgeNonOpp) ∧ (rc9_DeficitBridgeResidue → ReimerCardFormAll) := by
-- proof
  apply StatMech.Walls.rc9_cardform_symmetry_reduction


-- created on 2026-10-23
