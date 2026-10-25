import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc3_offsupportreaches
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc3_offSupportWalk_to_inducedReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_offsupportreaches.lean)
-/
@[path]
private lemma kc3_offSupportWalk_to_inducedReachable_eq
  {F : Set (Site 2)}
  {z e : Site 2}
  {p : (hypercubicLattice 2).Walk z e}
-- given
  (hz : z ∈ Fᶜ)
  (he : e ∈ Fᶜ)
  (hp : ∀ w ∈ p.support, w ∉ F) :
-- imply
  ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨z, hz⟩ ⟨e, he⟩ := by
-- proof
  apply StatMech.Walls.kc3_offSupportWalk_to_inducedReachable F hz he p hp

/--
[kc3_inducedReachable_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_offsupportreaches.lean)
-/
@[path]
private lemma kc3_inducedReachable_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z e : Site 2}
-- given
  (hz : z ∉ ({z | z ∈ Vc.support} : Set (Site 2)))
  (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
-- imply
  ∃ he : e ∈ ({z | z ∈ Vc.support} : Set (Site 2))ᶜ, ((hypercubicLattice 2).induce ({z | z ∈ Vc.support} : Set (Site 2))ᶜ).Reachable ⟨z, hz⟩ ⟨e, he⟩ := by
-- proof
  apply StatMech.Walls.kc3_inducedReachable_of_floodFill Vc hz h

/--
[kc3_offSupportReachesExterior_of_interiorSubset_and_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_offsupportreaches.lean)
-/
@[path]
private lemma kc3_offSupportReachesExterior_of_interiorSubset_and_outside_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hint : eaw_InteriorSubset K a)
  (hout : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  exc_OffSupportReachesExterior K a := by
-- proof
  apply StatMech.Walls.kc3_offSupportReachesExterior_of_interiorSubset_and_outside K a R hRbox hint hout

/--
[kc3_exterior_self_inducedReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_offsupportreaches.lean)
-/
@[path]
private lemma kc3_exterior_self_inducedReachable_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ((hypercubicLattice 2).induce ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable ⟨z, exterior_subset_compl _ R hR hz⟩ ⟨z, exterior_subset_compl _ R hR hz⟩ := by
-- proof
  apply StatMech.Walls.kc3_exterior_self_inducedReachable K a R hR z hz

/--
[kc3_unitCell_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_offsupportreaches.lean)
-/
@[path]
private lemma kc3_unitCell_interiorSubset_eq :
-- imply
  eaw_InteriorSubset unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc3_unitCell_interiorSubset

/--
[kc3_unitCell_loopSupportBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_offsupportreaches.lean)
-/
@[path]
private lemma kc3_unitCell_loopSupportBox_eq :
-- imply
  ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop unitCell ucBase).support} : Set (Site 2)) ⊆ box 2 R := by
-- proof
  apply StatMech.Walls.kc3_unitCell_loopSupportBox


-- created on 2026-10-23
