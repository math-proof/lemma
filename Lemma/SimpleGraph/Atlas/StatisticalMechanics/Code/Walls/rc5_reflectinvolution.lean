import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
open Finset StatMech StatMech.Walls


/--
[rc5_compl_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_compl_involutive_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rc5_compl_involutive

/--
[rc5_complEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_complEquiv_apply_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  rc5_complEquiv ω = rmr_compl ω := by
-- proof
  apply StatMech.Walls.rc5_complEquiv_apply ω

/--
[rc5_complEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_complEquiv_symm_apply_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  rc5_complEquiv.symm ω = rmr_compl ω := by
-- proof
  apply StatMech.Walls.rc5_complEquiv_symm_apply ω

/--
[rc5_complEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_complEquiv_symm_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc5_complEquiv : ConfigSpace α ≃ ConfigSpace α).symm = rc5_complEquiv := by
-- proof
  apply StatMech.Walls.rc5_complEquiv_symm

/--
[rc5_card_compl_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_card_compl_mem_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  #(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) := by
-- proof
  apply StatMech.Walls.rc5_card_compl_mem B

/--
[rc5_card_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_card_reflect_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ rmr_reflect B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) := by
-- proof
  apply StatMech.Walls.rc5_card_reflect B

/--
[rc5_RHS_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_RHS_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc5_RHS_eq_inter A B

/--
[rc5_reimerCardForm_iff_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_reimerCardForm_iff_deficit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_iff_deficit A B

/--
[rc5_deficit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_deficit_eq_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc5_deficit A B = (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ) - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ) := by
-- proof
  apply StatMech.Walls.rc5_deficit_eq A B

/--
[rc5_deficitNonpos_iff_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_deficitNonpos_iff_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_DeficitNonpos ↔ ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc5_deficitNonpos_iff_reimerCardFormAll

/--
[rc5_deficit_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_deficit_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_deficit rbi_A rbi_B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc5_deficit_rbi

/--
[rc5_deficit_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_deficit_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc5_deficit_of_disjoint_support hA hB hST

/--
[rc5_deficit_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_deficit_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc5_deficit_of_box_empty hbox

/--
[rc5_deficit_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_deficit_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc5_deficit_one A B

/--
[rc5_reflect_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean)
-/
@[path]
private lemma rc5_reflect_involution_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B))) ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))) ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) := by
-- proof
  apply StatMech.Walls.rc5_reflect_involution A B


-- created on 2026-10-23
