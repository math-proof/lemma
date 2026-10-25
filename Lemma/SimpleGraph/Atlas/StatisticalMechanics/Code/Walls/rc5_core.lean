import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part3
open Finset StatMech StatMech.Walls


/--
[rc5_core_reimerCardForm_iff_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reimerCardForm_iff_deficit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc5_core_reimerCardForm_iff_deficit A B

/--
[rc5_core_deficitNonpos_iff_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_deficitNonpos_iff_reimerCardFormAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_DeficitNonpos ↔ ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc5_core_deficitNonpos_iff_reimerCardFormAll

/--
[rc5_core_compressionEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_compressionEngine_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ) ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc5_core_compressionEngine 𝒜 ℬ

/--
[rc5_core_reflectionDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reflectionDeficit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))) ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) := by
-- proof
  apply StatMech.Walls.rc5_core_reflectionDeficit A B

/--
[rc5_core_reindexTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reindexTransfer_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_core_reindexTransfer hcard A B

/--
[rc5_core_reimerCardForm_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reimerCardForm_of_injection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : rc5_BoxReflectInjection A B) :
-- imply
  StatMech.poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_core_reimerCardForm_of_injection h

/--
[rc5_core_injection_of_reimerCardForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injection_of_reimerCardForm_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : StatMech.poc_ReimerCardForm A B) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc5_core_injection_of_reimerCardForm h

/--
[rc5_core_injection_iff_reimerCardForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injection_iff_reimerCardForm_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc5_BoxReflectInjection A B ↔ StatMech.poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_core_injection_iff_reimerCardForm A B

/--
[rc5_core_reimerCardFormAll_of_injectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reimerCardFormAll_of_injectionAll_eq
-- given
  (h : rc5_BoxReflectInjectionAll) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc5_core_reimerCardFormAll_of_injectionAll h

/--
[rc5_core_injectionAll_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injectionAll_of_reimerCardFormAll_eq
-- given
  (h : ReimerCardFormAll) :
-- imply
  rc5_BoxReflectInjectionAll := by
-- proof
  apply StatMech.Walls.rc5_core_injectionAll_of_reimerCardFormAll h

/--
[rc5_core_injectionAll_iff_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injectionAll_iff_reimerCardFormAll_eq :
-- imply
  rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc5_core_injectionAll_iff_reimerCardFormAll

/--
[rc5_core_reimerCardFormAll_iff_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reimerCardFormAll_iff_residue_eq :
-- imply
  ReimerCardFormAll ↔ ReimerResidue := by
-- proof
  apply StatMech.Walls.rc5_core_reimerCardFormAll_iff_residue

/--
[rc5_core_injectionAll_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injectionAll_of_residue_eq
-- given
  (h : ReimerResidue) :
-- imply
  rc5_BoxReflectInjectionAll := by
-- proof
  apply StatMech.Walls.rc5_core_injectionAll_of_residue h

/--
[rc5_core_reimer_inequality_of_injectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_reimer_inequality_of_injectionAll_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc5_BoxReflectInjectionAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc5_core_reimer_inequality_of_injectionAll h hp A B

/--
[rc5_core_injection_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injection_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_BoxReflectInjection rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc5_core_injection_rbi

/--
[rc5_core_injection_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injection_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc5_core_injection_of_disjoint_support hA hB hST

/--
[rc5_core_injection_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injection_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc5_core_injection_of_box_empty hbox

/--
[rc5_core_injection_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_injection_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc5_core_injection_one A B

/--
[rc5_core_cardform_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean)
-/
@[path]
private lemma rc5_core_cardform_all_eq :
-- imply
  (rc5_DeficitNonpos ↔ ReimerCardFormAll) ∧ (ReimerCardFormAll ↔ ReimerResidue) ∧ (rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll) ∧ (rc5_BoxReflectInjectionAll → ReimerResidue) ∧ (ReimerResidue → rc5_BoxReflectInjectionAll) := by
-- proof
  apply StatMech.Walls.rc5_core_cardform_all


-- created on 2026-10-23
