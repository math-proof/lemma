import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc7core.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc7_even_of_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_even_of_infiniteComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
  (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc7_even_of_infiniteComponent Vc R hsupp hzmem hinf

/--
[kc7_mem_compl_leftRegion_of_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_mem_compl_leftRegion_of_infiniteComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
  (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite) :
-- imply
  z ∈ (jec_leftRegion Vc)ᶜ := by
-- proof
  apply StatMech.Walls.kc7_mem_compl_leftRegion_of_infiniteComponent Vc R hsupp hzmem hinf

/--
[kc7_offSupportOutsideInK_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_offSupportOutsideInK_of_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hres : kc7_OffSupportOutsideInfinite K a) :
-- imply
  kc6_OffSupportOutsideInK K a := by
-- proof
  apply StatMech.Walls.kc7_offSupportOutsideInK_of_infinite K a R hRbox hres

/--
[kc7_interiorSubset_of_supportOdd_and_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_interiorSubset_of_supportOdd_and_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hsupp : exc_SupportOddInK K a)
  (hres : kc7_OffSupportOutsideInfinite K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc7_interiorSubset_of_supportOdd_and_infinite K a R hRbox hsupp hres

/--
[kc7_leftRegion_eq_of_supportOdd_winding_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_leftRegion_eq_of_supportOdd_winding_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hsupp : exc_SupportOddInK K a)
  (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a))
  (hres : kc7_OffSupportOutsideInfinite K a) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc7_leftRegion_eq_of_supportOdd_winding_infinite K a R hRbox hsupp hwind hres

/--
[kc7_bdEdgeMatch_of_supportOdd_winding_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_bdEdgeMatch_of_supportOdd_winding_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hsupp : exc_SupportOddInK K a)
  (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a))
  (hres : kc7_OffSupportOutsideInfinite K a) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc7_bdEdgeMatch_of_supportOdd_winding_infinite K a R hRbox hsupp hwind hres

/--
[kc7_offSupport_inside_subset_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_offSupport_inside_subset_of_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hres : kc7_OffSupportOutsideInfinite K a) :
-- imply
  ∀ z, z ∉ (mpl_orbitLoop K a).support → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K := by
-- proof
  apply StatMech.Walls.kc7_offSupport_inside_subset_of_infinite K a R hRbox hres

/--
[kc7_exterior_satisfies_residue_conclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_exterior_satisfies_residue_conclusion_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ hzmem : z ∈ (oc_supportSet (mpl_orbitLoop K a))ᶜ, (((hypercubicLattice 2).induce (oc_supportSet (mpl_orbitLoop K a))ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc7_exterior_satisfies_residue_conclusion K a R hRbox hz

/--
[kc7_residue_conclusion_inhabited](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_residue_conclusion_inhabited_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hKbox : K ⊆ box 2 R)
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R) :
-- imply
  ∃ z : Site 2, z ∉ K ∧ z ∉ (mpl_orbitLoop K a).support ∧ ∃ hzmem : z ∈ (oc_supportSet (mpl_orbitLoop K a))ᶜ, (((hypercubicLattice 2).induce (oc_supportSet (mpl_orbitLoop K a))ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc7_residue_conclusion_inhabited K a R hKbox hRbox

/--
[kc7_unitCell_offSupportOutsideInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean)
-/
@[path]
private lemma kc7_unitCell_offSupportOutsideInK_eq
  {a : Site 2} :
-- imply
  kc6_OffSupportOutsideInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc7_unitCell_offSupportOutsideInK


-- created on 2026-10-23
