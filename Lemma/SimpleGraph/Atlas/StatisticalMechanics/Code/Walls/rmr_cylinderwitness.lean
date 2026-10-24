import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rmr_cylinderwitness
open Finset StatMech StatMech.Walls


/--
[mem_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma mem_cylinder_eq
  {K : Finset E}
  {ω ω' : ConfigSpace E} :
-- imply
  ω' ∈ cylinder K ω ↔ ∀ e ∈ K, ω' e = ω e := by
-- proof
  apply StatMech.Walls.mem_cylinder

/--
[self_mem_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma self_mem_cylinder_eq
  {K : Finset E}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ cylinder K ω := by
-- proof
  apply StatMech.Walls.self_mem_cylinder K ω

/--
[cylinder_subset_iff_occursOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma cylinder_subset_iff_occursOn_eq
  {A : Set (ConfigSpace E)}
  {K : Finset E}
  {ω : ConfigSpace E} :
-- imply
  cylinder K ω ⊆ A ↔ OccursOn A (↑K) ω := by
-- proof
  apply StatMech.Walls.cylinder_subset_iff_occursOn

/--
[cylinder_subset_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma cylinder_subset_of_subset_eq
  {K K' : Finset E}
  {ω : ConfigSpace E}
-- given
  (h : K ⊆ K') :
-- imply
  cylinder K' ω ⊆ cylinder K ω := by
-- proof
  apply StatMech.Walls.cylinder_subset_of_subset h ω

/--
[cylinder_subset_A_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma cylinder_subset_A_mono_eq
  {A : Set (ConfigSpace E)}
  {K K' : Finset E}
  {ω : ConfigSpace E}
-- given
  (h : K ⊆ K')
  (hA : cylinder K ω ⊆ A) :
-- imply
  cylinder K' ω ⊆ A := by
-- proof
  apply StatMech.Walls.cylinder_subset_A_mono h ω hA

/--
[exists_minimal_cylinder_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma exists_minimal_cylinder_witness_eq
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {K : Finset E}
-- given
  (hK : cylinder K ω ⊆ A) :
-- imply
  ∃ K₀ ⊆ K, Minimal (fun S => cylinder S ω ⊆ A) K₀ := by
-- proof
  apply StatMech.Walls.exists_minimal_cylinder_witness hK

/--
[mem_disjointOccurrence_iff_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma mem_disjointOccurrence_iff_cylinder_eq
  [Finite E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ K L : Finset E, Disjoint K L ∧ cylinder K ω ⊆ A ∧ cylinder L ω ⊆ B := by
-- proof
  apply StatMech.Walls.mem_disjointOccurrence_iff_cylinder

/--
[mem_disjointOccurrence_iff_minimal_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma mem_disjointOccurrence_iff_minimal_cylinder_eq
  [Finite E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ K L : Finset E, Disjoint K L ∧ Minimal (fun S => cylinder S ω ⊆ A) K ∧ Minimal (fun S => cylinder S ω ⊆ B) L := by
-- proof
  apply StatMech.Walls.mem_disjointOccurrence_iff_minimal_cylinder

/--
[cylinder_filter_subset_iff_occursOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma cylinder_filter_subset_iff_occursOn_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
  {wK : E → Bool} :
-- imply
  cylinder (Finset.univ.filter (fun a => wK a = true)) ω ⊆ A ↔ OccursOn A {a | wK a = true} ω := by
-- proof
  apply StatMech.Walls.cylinder_filter_subset_iff_occursOn wK

/--
[slabBox_top_eq_cylinderWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean)
-/
@[path]
private lemma slabBox_top_eq_cylinderWitness_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)} :
-- imply
  (StatMech.poc_slabBox A B StatMech.poc_topKey : Finset (ConfigSpace E)) = Finset.univ.filter (fun ω => ∃ K L : Finset E, Disjoint K L ∧ cylinder K ω ⊆ A ∧ cylinder L ω ⊆ B) := by
-- proof
  apply StatMech.Walls.slabBox_top_eq_cylinderWitness A B


-- created on 2026-10-23
