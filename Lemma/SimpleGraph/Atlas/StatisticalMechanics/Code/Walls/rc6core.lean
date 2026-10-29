import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
open Finset StatMech StatMech.Walls


/--
[rc6_canonMirror_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_canonMirror_mem_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ disjointOccurrence A B) :
-- imply
  rc6_canonMirror A B ω ∈ A ∩ rmr_reflect B := by
-- proof
  apply StatMech.Walls.rc6_canonMirror_mem A B hω

/--
[rc6_canonMirror_mapsTo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_canonMirror_mapsTo_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  Set.MapsTo (rc6_canonMirror A B) (disjointOccurrence A B) (A ∩ rmr_reflect B) := by
-- proof
  apply StatMech.Walls.rc6_canonMirror_mapsTo A B

/--
[rc6_boxReflectInjection_of_canonMirror_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_boxReflectInjection_of_canonMirror_injOn_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hinj : Set.InjOn (rc6_canonMirror A B) {ω | ω ∈ disjointOccurrence A B}) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc6_boxReflectInjection_of_canonMirror_injOn A B hinj

/--
[rc6_boxReflectInjection_of_mirrorInjectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_boxReflectInjection_of_mirrorInjectivity_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : rc6_MirrorInjectivity A B) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc6_boxReflectInjection_of_mirrorInjectivity A B h

/--
[rc6_witnessTied_injectivity_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_witnessTied_injectivity_false_eq :
-- imply
  ¬ poc_WitnessInjection rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc6_witnessTied_injectivity_false

/--
[rc6_reimerCardFormAll_of_mirrorInjectivityAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_reimerCardFormAll_of_mirrorInjectivityAll_eq
-- given
  (h : rc6_MirrorInjectivityAll) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc6_reimerCardFormAll_of_mirrorInjectivityAll h

/--
[rc6_injectionAll_iff_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_injectionAll_iff_reimerCardFormAll_eq :
-- imply
  rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc6_injectionAll_iff_reimerCardFormAll

/--
[rc6_reimer_inequality_of_injectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_reimer_inequality_of_injectionAll_eq
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc5_BoxReflectInjectionAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc6_reimer_inequality_of_injectionAll h hp A B

/--
[rc6_compressionEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_compressionEngine_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ) ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc6_compressionEngine 𝒜 ℬ

/--
[rc6_cardform_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_cardform_all_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (∀ ω, ω ∈ disjointOccurrence A B → rc6_canonMirror A B ω ∈ A ∩ rmr_reflect B) ∧ (rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll) ∧ (ReimerCardFormAll ↔ ReimerResidue) ∧ (rc6_MirrorInjectivityAll → ReimerCardFormAll) ∧ ¬ poc_WitnessInjection rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc6_cardform_all A B

/--
[rc6_injection_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_injection_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc5_BoxReflectInjection rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc6_injection_rbi

/--
[rc6_injection_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_injection_of_disjoint_support_eq
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
  apply StatMech.Walls.rc6_injection_of_disjoint_support hA hB hST

/--
[rc6_injection_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_injection_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc6_injection_of_box_empty hbox

/--
[rc6_injection_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean)
-/
@[path]
private lemma rc6_injection_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  rc5_BoxReflectInjection A B := by
-- proof
  apply StatMech.Walls.rc6_injection_one A B


-- created on 2026-10-23
