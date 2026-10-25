import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc13core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc13_mem_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_mem_compl_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support) :
-- imply
  z ∈ (oc_supportSet Vc)ᶜ := by
-- proof
  apply StatMech.Walls.kc13_mem_compl Vc hz

/--
[kc13_reachesFarLeftBeacon_of_noFiniteHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_reachesFarLeftBeacon_of_noFiniteHole_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hres : kc13_NoFiniteHole Vc) :
-- imply
  kc12_ReachesFarLeftBeacon Vc R := by
-- proof
  apply StatMech.Walls.kc13_reachesFarLeftBeacon_of_noFiniteHole Vc R hsupp hres

/--
[kc13_noFiniteHole_of_reachesFarLeftBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_noFiniteHole_of_reachesFarLeftBeacon_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hres : kc12_ReachesFarLeftBeacon Vc R) :
-- imply
  kc13_NoFiniteHole Vc := by
-- proof
  apply StatMech.Walls.kc13_noFiniteHole_of_reachesFarLeftBeacon Vc R hsupp hres

/--
[kc13_reachesFarLeftBeacon_iff_noFiniteHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_reachesFarLeftBeacon_iff_noFiniteHole_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  kc12_ReachesFarLeftBeacon Vc R ↔ kc13_NoFiniteHole Vc := by
-- proof
  apply StatMech.Walls.kc13_reachesFarLeftBeacon_iff_noFiniteHole Vc R hsupp

/--
[kc13_offSupport_reachable_iff_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_offSupport_reachable_iff_induce_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z y : Site 2}
-- given
  (hz : z ∈ (oc_supportSet Vc)ᶜ)
  (hy : y ∈ (oc_supportSet Vc)ᶜ) :
-- imply
  (offSupport Vc).Reachable z y ↔ ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨z, hz⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.kc13_offSupport_reachable_iff_induce Vc hz hy

/--
[kc13_component_finite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_component_finite_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hzmem : z ∈ (oc_supportSet Vc)ᶜ) :
-- imply
  (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Finite ↔ (kc12_component Vc z).Finite := by
-- proof
  apply StatMech.Walls.kc13_component_finite_iff Vc hz hzmem

/--
[kc13_neighbour_in_component_or_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_neighbour_in_component_or_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {w w' : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hwC : w ∈ kc12_component Vc z)
  (hadj : (hypercubicLattice 2).Adj w w') :
-- imply
  w' ∈ kc12_component Vc z ∨ w' ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc13_neighbour_in_component_or_onSupport Vc hz hwC hadj

/--
[kc13_finiteComponent_boundary_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_finiteComponent_boundary_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {w w' : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hwC : w ∈ kc12_component Vc z)
  (hadj : (hypercubicLattice 2).Adj w w')
  (hw'notC : w' ∉ kc12_component Vc z) :
-- imply
  w' ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc13_finiteComponent_boundary_onSupport Vc hz hwC hadj hw'notC

/--
[kc13_finiteComponent_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_finiteComponent_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {w : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hzout : z ∉ jec_leftRegion Vc)
  (hwC : w ∈ kc12_component Vc z) :
-- imply
  w ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc13_finiteComponent_outside Vc hz hzout hwC

/--
[kc13_target_fails_iff_finite_evenComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_target_fails_iff_finite_evenComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  ¬ kc12_ReachesFarLeftBeacon Vc R ↔ ∃ z : Site 2, z ∉ Vc.support ∧ z ∉ jec_leftRegion Vc ∧ (kc12_component Vc z).Finite := by
-- proof
  apply StatMech.Walls.kc13_target_fails_iff_finite_evenComponent Vc R hsupp

/--
[kc13_offSupportOutsideInfinite_of_noFiniteHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_offSupportOutsideInfinite_of_noFiniteHole_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hres : kc13_NoFiniteHole (mpl_orbitLoop K a)) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc13_offSupportOutsideInfinite_of_noFiniteHole K a R hRbox hbridge hres

/--
[kc13_unitCell_noFiniteHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_unitCell_noFiniteHole_eq
  {a : Site 2} :
-- imply
  kc13_NoFiniteHole (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc13_unitCell_noFiniteHole

/--
[kc13_unitCell_reachesFarLeftBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc13core.lean)
-/
@[path]
private lemma kc13_unitCell_reachesFarLeftBeacon_eq
  {a : Site 2} :
-- imply
  kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc13_unitCell_reachesFarLeftBeacon


-- created on 2026-10-23
