import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc3_core
open Finset StatMech StatMech.Walls


/--
[rc3_core_reimerCardFormAll_of_slabCardAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerCardFormAll_of_slabCardAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : StatMech.poc_SlabCardAll) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc3_core_reimerCardFormAll_of_slabCardAll h

/--
[rc3_core_perKey_top_iff_reimerCardForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_perKey_top_iff_reimerCardForm_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc3_PerKey A B poc_topKey ↔ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc3_core_perKey_top_iff_reimerCardForm A B

/--
[rc3_core_provedDAG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_provedDAG_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ) ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc3_core_provedDAG 𝒜 ℬ

/--
[rc3_core_residue_iff_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_residue_iff_bridge_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerResidue ↔ rc_core_CountBoxBridge := by
-- proof
  apply StatMech.Walls.rc3_core_residue_iff_bridge

/--
[rc3_core_residue_iff_perKeyAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_residue_iff_perKeyAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerResidue ↔ rc3_PerKeyAll := by
-- proof
  apply StatMech.Walls.rc3_core_residue_iff_perKeyAll

/--
[rc3_core_residue_iff_slabInjectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_residue_iff_slabInjectionAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerResidue ↔ SlabInjectionAll := by
-- proof
  apply StatMech.Walls.rc3_core_residue_iff_slabInjectionAll

/--
[rc3_core_reimerWprobCore_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerWprobCore_of_residue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : ReimerResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc3_core_reimerWprobCore_of_residue h

/--
[rc3_core_reimer_inequality_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimer_inequality_of_residue_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : ReimerResidue)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc3_core_reimer_inequality_of_residue h hp A B

/--
[rc3_core_slab_frozen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_slab_frozen_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (hk : ω ∈ rc2_slab k)
  (hne : k.1 a = k.2 a) :
-- imply
  ω a = k.1 a := by
-- proof
  apply StatMech.Walls.rc3_core_slab_frozen hk a hne

/--
[rc3_core_slab_differ_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_slab_differ_key_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (hk : ω ∈ rc2_slab k)
  (hne : k.1 a ≠ k.2 a) :
-- imply
  k.1 a = true ∧ k.2 a = false := by
-- proof
  apply StatMech.Walls.rc3_core_slab_differ_key hk a hne

/--
[rc3_core_slab_of_frozen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_slab_of_frozen_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
-- given
  (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false))
  (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a) :
-- imply
  ω ∈ rc2_slab k := by
-- proof
  apply StatMech.Walls.rc3_core_slab_of_frozen hvalid hfroz

/--
[rc3_core_orbitKey_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_orbitKey_valid_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {a : α}
-- given
  (hne : (orbitKey p).1 a ≠ (orbitKey p).2 a) :
-- imply
  (orbitKey p).1 a = true ∧ (orbitKey p).2 a = false := by
-- proof
  apply StatMech.Walls.rc3_core_orbitKey_valid p a hne

/--
[rc3_core_residue_of_subcubeReduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_residue_of_subcubeReduction_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (hred : ReimerSubcubeReduction)
  (hcard : ReimerCardFormAll) :
-- imply
  ReimerResidue := by
-- proof
  apply StatMech.Walls.rc3_core_residue_of_subcubeReduction hred hcard

/--
[rc3_core_reimer_inequality_of_subcubeReduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimer_inequality_of_subcubeReduction_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hred : ReimerSubcubeReduction)
  (hcard : ReimerCardFormAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc3_core_reimer_inequality_of_subcubeReduction hred hcard hp A B

/--
[rc3_core_reimerCardFormAll_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerCardFormAll_of_residue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : ReimerResidue) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc3_core_reimerCardFormAll_of_residue h

/--
[rc3_core_reimerCardForm_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerCardForm_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_ReimerCardForm rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc3_core_reimerCardForm_rbi

/--
[rc3_core_reimerCardForm_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerCardForm_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc3_core_reimerCardForm_of_disjoint_support hA hB hST

/--
[rc3_core_reimerCardForm_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerCardForm_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc3_core_reimerCardForm_of_box_empty hbox

/--
[rc3_core_reimerCardForm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_reimerCardForm_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc3_core_reimerCardForm_one A B

/--
[rc3_core_count_box_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean)
-/
@[path]
private lemma rc3_core_count_box_bridge_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (ReimerResidue ↔ rc_core_CountBoxBridge) ∧ (ReimerResidue ↔ rc3_PerKeyAll) ∧ (ReimerResidue ↔ SlabInjectionAll) ∧ (ReimerResidue → ReimerWprobCore) ∧ (ReimerResidue → ReimerCardFormAll) ∧ (ReimerSubcubeReduction → ReimerCardFormAll → ReimerResidue) := by
-- proof
  apply StatMech.Walls.rc3_core_count_box_bridge


-- created on 2026-10-23
