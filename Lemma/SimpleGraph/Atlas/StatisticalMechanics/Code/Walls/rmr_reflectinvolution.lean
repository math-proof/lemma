import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rmr_reflectinvolution
open Finset StatMech StatMech.Walls


/--
[rmr_compl_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_compl_apply_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α}
  {a : α} :
-- imply
  rmr_compl ω a = !ω a := by
-- proof
  apply StatMech.Walls.rmr_compl_apply ω a

/--
[rmr_compl_eq_keyFlip_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_compl_eq_keyFlip_top_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  rmr_compl ω = StatMech.poc_keyFlip (StatMech.poc_topKey : ConfigSpace α × ConfigSpace α) ω := by
-- proof
  apply StatMech.Walls.rmr_compl_eq_keyFlip_top ω

/--
[rmr_compl_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_compl_involutive_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rmr_compl_involutive

/--
[rmr_compl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_compl_injective_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  Function.Injective (rmr_compl : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rmr_compl_injective

/--
[rmr_compl_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_compl_bijective_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  Function.Bijective (rmr_compl : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rmr_compl_bijective

/--
[rmr_compl_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_compl_compl_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  rmr_compl (rmr_compl ω) = ω := by
-- proof
  apply StatMech.Walls.rmr_compl_compl ω

/--
[rmr_card_compl_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_card_compl_mem_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  #(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) := by
-- proof
  apply StatMech.Walls.rmr_card_compl_mem B

/--
[rmr_mem_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_mem_reflect_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rmr_reflect B ↔ rmr_compl ω ∈ B := by
-- proof
  apply StatMech.Walls.rmr_mem_reflect B ω

/--
[rmr_reflect_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_reflect_reflect_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  rmr_reflect (rmr_reflect B) = B := by
-- proof
  apply StatMech.Walls.rmr_reflect_reflect B

/--
[rmr_card_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_card_reflect_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ rmr_reflect B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) := by
-- proof
  apply StatMech.Walls.rmr_card_reflect B

/--
[rmr_RHS_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_RHS_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rmr_RHS_eq_inter A B

/--
[rmr_reimerCardForm_iff_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean)
-/
@[path]
private lemma rmr_reimerCardForm_iff_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rmr_reimerCardForm_iff_inter A B


-- created on 2026-10-23
