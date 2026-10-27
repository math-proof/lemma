import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc15core.Part3
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc15_facialOrbit_ne_of_component_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_facialOrbit_ne_of_component_ne_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s t : Site 2}
-- given
  (hs : s ∉ Vc.support)
  (hne : offSupportComponent Vc s ≠ offSupportComponent Vc t) :
-- imply
  {e : Dart | IsBoundaryDart (offSupportComponent Vc s) e} ≠ {e : Dart | IsBoundaryDart (offSupportComponent Vc t) e} := by
-- proof
  apply StatMech.Walls.kc15_facialOrbit_ne_of_component_ne Vc hs hne

/--
[kc15_beacon_component_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_beacon_component_infinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)).Infinite := by
-- proof
  apply StatMech.Walls.kc15_beacon_component_infinite Vc R hsupp

/--
[kc15_beacon_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_beacon_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc15_beacon_offSupport Vc R hsupp

/--
[kc15_beacon_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_beacon_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc15_beacon_outside Vc R hsupp

/--
[kc15_finiteComponent_ne_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_finiteComponent_ne_beacon_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hfin : (offSupportComponent Vc z).Finite) :
-- imply
  offSupportComponent Vc z ≠ offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2) := by
-- proof
  apply StatMech.Walls.kc15_finiteComponent_ne_beacon Vc R hsupp hfin

/--
[kc15_outsideComponent_ne_insideComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_outsideComponent_ne_insideComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z x : Site 2}
-- given
  (hzout : z ∉ jec_leftRegion Vc)
  (hzoff : z ∉ Vc.support)
  (hxin : x ∈ jec_leftRegion Vc) :
-- imply
  offSupportComponent Vc z ≠ offSupportComponent Vc x := by
-- proof
  apply StatMech.Walls.kc15_outsideComponent_ne_insideComponent Vc hzout hzoff hxin

/--
[kc15_secondBoundedRegion_third_facialOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_secondBoundedRegion_third_facialOrbit_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z x : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzoff : z ∉ Vc.support)
  (hzout : z ∉ jec_leftRegion Vc)
  (hfin : (offSupportComponent Vc z).Finite)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support) :
-- imply
  {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠ {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ∧ {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠ {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} ∧ {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ≠ {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} := by
-- proof
  apply StatMech.Walls.kc15_secondBoundedRegion_third_facialOrbit Vc R hsupp hzoff hzout hfin hxin hxoff

/--
[kc15_facialOrbit_mem_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_facialOrbit_mem_family_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hres : kc15_FacialOrbitFamilyTwo Vc R x) :
-- imply
  {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} = {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ∨ {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} = {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} := by
-- proof
  apply StatMech.Walls.kc15_facialOrbit_mem_family Vc R hz hres

/--
[kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hres : kc15_FacialOrbitFamilyTwo Vc R x) :
-- imply
  kc14_NoSecondBoundedRegion Vc := by
-- proof
  apply StatMech.Walls.kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo Vc R hsupp hxin hxoff hres

/--
[kc15_offSupportOutsideInfinite_of_facialOrbitFamilyTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_offSupportOutsideInfinite_of_facialOrbitFamilyTwo_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {x : Site 2}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hxin : x ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hxoff : x ∉ (mpl_orbitLoop K a).support)
  (hres : kc15_FacialOrbitFamilyTwo (mpl_orbitLoop K a) R x) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc15_offSupportOutsideInfinite_of_facialOrbitFamilyTwo K a R hRbox hbridge hxin hxoff hres

/--
[kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hres : kc15_OutsideOneFacialOrbit Vc R) :
-- imply
  kc14_NoSecondBoundedRegion Vc := by
-- proof
  apply StatMech.Walls.kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit Vc R hsupp hres

/--
[kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hres : kc12_ReachesFarLeftBeacon Vc R) :
-- imply
  kc15_OutsideOneFacialOrbit Vc R := by
-- proof
  apply StatMech.Walls.kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon Vc R hres

/--
[kc15_facialOrbitFamilyTwo_of_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_facialOrbitFamilyTwo_of_sides_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ w ∈ p.support, w ∉ Vc.support)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  kc15_FacialOrbitFamilyTwo Vc R x := by
-- proof
  apply StatMech.Walls.kc15_facialOrbitFamilyTwo_of_sides Vc R hsupp hxin hxoff hin hout

/--
[kc15_unitCell_outsideOneFacialOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_unitCell_outsideOneFacialOrbit_eq
  {a : Site 2} :
-- imply
  kc15_OutsideOneFacialOrbit (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc15_unitCell_outsideOneFacialOrbit

/--
[kc15_unitCell_noSecondBoundedRegion_via_facialOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_unitCell_noSecondBoundedRegion_via_facialOrbit_eq
  {a : Site 2} :
-- imply
  kc14_NoSecondBoundedRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc15_unitCell_noSecondBoundedRegion_via_facialOrbit

/--
[kc15_unitCell_finiteComponent_facialOrbit_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean)
-/
@[path]
private lemma kc15_unitCell_finiteComponent_facialOrbit_ne_eq
  {a : Site 2}
  {z : Site 2}
-- given
  (hzoff : z ∉ (mpl_orbitLoop unitCell ucBase).support)
  (hfin : (offSupportComponent (mpl_orbitLoop unitCell ucBase) z).Finite) :
-- imply
  {e : Dart | IsBoundaryDart (offSupportComponent (mpl_orbitLoop unitCell ucBase) z) e} ≠ {e : Dart | IsBoundaryDart (offSupportComponent (mpl_orbitLoop unitCell ucBase) (![-((1 : ℤ) + 1), 0] : Site 2)) e} := by
-- proof
  apply StatMech.Walls.kc15_unitCell_finiteComponent_facialOrbit_ne z hzoff hfin


-- created on 2026-10-23
