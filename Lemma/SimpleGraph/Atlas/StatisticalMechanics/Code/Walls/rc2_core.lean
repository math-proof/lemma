import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc2_core
open Finset StatMech StatMech.Walls


/--
[rc2_slabBox_eq_slabFilter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabBox_eq_slabFilter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  poc_slabBox A B k = Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc2_slabBox_eq_slabFilter A B k

/--
[rc2_slabCard_iff_perKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabCard_iff_perKey_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_SlabCard A B ↔ ∀ k : ConfigSpace α × ConfigSpace α, #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤ #(Finset.univ.filter (fun ω => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)) := by
-- proof
  apply StatMech.Walls.rc2_slabCard_iff_perKey A B

/--
[rc2_orbitKey_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_orbitKey_symm_eq
  [Fintype α]
  [DecidableEq α]
  {a b : ConfigSpace α} :
-- imply
  orbitKey (a, b) = orbitKey (b, a) := by
-- proof
  apply StatMech.Walls.rc2_orbitKey_symm a b

/--
[rc2_keyFlip_slab_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_keyFlip_slab_invol_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  poc_keyFlip k (poc_keyFlip k ω) = ω := by
-- proof
  apply StatMech.Walls.rc2_keyFlip_slab_invol k ω

/--
[rc2_keyFlip_maps_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_keyFlip_maps_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ rc2_slab k) :
-- imply
  poc_keyFlip k ω ∈ rc2_slab k := by
-- proof
  apply StatMech.Walls.rc2_keyFlip_maps_slab k hω

/--
[rc2_slabInjection_imp_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabInjection_imp_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : SlabInjection A B) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc2_slabInjection_imp_slabCard h

/--
[rc2_slabInjection_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabInjection_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  SlabInjection A B := by
-- proof
  apply StatMech.Walls.rc2_slabInjection_of_slabCard h

/--
[rc2_slabInjection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabInjection_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  SlabInjection A B ↔ poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc2_slabInjection_iff A B

/--
[rc2_slabCardAll_of_slabInjectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabCardAll_of_slabInjectionAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : SlabInjectionAll) :
-- imply
  StatMech.poc_SlabCardAll := by
-- proof
  apply StatMech.Walls.rc2_slabCardAll_of_slabInjectionAll h

/--
[rc2_reimerWprobCore_of_slabInjectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_reimerWprobCore_of_slabInjectionAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : SlabInjectionAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc2_reimerWprobCore_of_slabInjectionAll h

/--
[rc2_reimer_inequality_of_slabInjectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_reimer_inequality_of_slabInjectionAll_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : SlabInjectionAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc2_reimer_inequality_of_slabInjectionAll h hp A B

/--
[rc2_compressionEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_compressionEngine_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc2_compressionEngine 𝒜 ℬ

/--
[rc2_engine_count_eq_doubledBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_engine_count_eq_doubledBox_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc2_engine_count_eq_doubledBox 𝒜 ℬ

/--
[rc2_slabCard_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabCard_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc2_slabCard_of_disjoint_support hA hB hST

/--
[rc2_slabCard_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabCard_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc2_slabCard_one A B

/--
[rc2_slabCard_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabCard_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc2_slabCard_of_box_empty hbox

/--
[rc2_slabCard_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabCard_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_SlabCard rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc2_slabCard_rbi

/--
[rc2_perKey_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_perKey_rbi_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence rbi_A rbi_B ∧ ω ∈ rc2_slab k)) ≤ #(Finset.univ.filter (fun ω => ω ∈ rbi_A ∩ rc2_keyReflect k rbi_B ∧ ω ∈ rc2_slab k)) := by
-- proof
  apply StatMech.Walls.rc2_perKey_rbi k

/--
[rc2_slabInjection_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabInjection_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  SlabInjection rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc2_slabInjection_rbi

/--
[rc2_slabInjection_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabInjection_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  SlabInjection A B := by
-- proof
  apply StatMech.Walls.rc2_slabInjection_of_disjoint_support hA hB hST

/--
[rc2_slabInjection_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_slabInjection_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  SlabInjection A B := by
-- proof
  apply StatMech.Walls.rc2_slabInjection_one A B

/--
[rc2_count_box_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean)
-/
@[path]
private lemma rc2_count_box_bridge_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ {α : Type} [Fintype α] [DecidableEq α] (A B : Set (ConfigSpace α)), poc_SlabCard A B ↔ ∀ k : ConfigSpace α × ConfigSpace α, #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤ #(Finset.univ.filter (fun ω => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k))) ∧ (SlabInjectionAll → StatMech.poc_SlabCardAll) ∧ (SlabInjectionAll → rc_core_CountBoxBridge) ∧ (SlabInjectionAll → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc2_count_box_bridge


-- created on 2026-10-23
