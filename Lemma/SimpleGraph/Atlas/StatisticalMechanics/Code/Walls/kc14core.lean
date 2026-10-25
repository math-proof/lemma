import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc14core.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc14_finiteEvenComponent_disjoint_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_finiteEvenComponent_disjoint_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hzout : z ∉ jec_leftRegion Vc) :
-- imply
  Disjoint (kc12_component Vc z) (jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc14_finiteEvenComponent_disjoint_leftRegion Vc hz hzout

/--
[kc14_finiteEvenComponent_second_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_finiteEvenComponent_second_region_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hzout : z ∉ jec_leftRegion Vc)
  (hfin : (kc12_component Vc z).Finite) :
-- imply
  (kc12_component Vc z).Finite ∧ (∀ w ∈ kc12_component Vc z, w ∉ jec_leftRegion Vc) ∧ (∀ w ∈ kc12_component Vc z, ∀ w2 : Site 2, (hypercubicLattice 2).Adj w w2 → w2 ∉ kc12_component Vc z → w2 ∈ Vc.support) ∧ Disjoint (kc12_component Vc z) (jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc14_finiteEvenComponent_second_region Vc hz hzout hfin

/--
[kc14_noFiniteHole_of_noSecondBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_noFiniteHole_of_noSecondBoundedRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hres : kc14_NoSecondBoundedRegion Vc) :
-- imply
  kc13_NoFiniteHole Vc := by
-- proof
  apply StatMech.Walls.kc14_noFiniteHole_of_noSecondBoundedRegion Vc hres

/--
[kc14_noSecondBoundedRegion_of_noFiniteHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_noSecondBoundedRegion_of_noFiniteHole_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hres : kc13_NoFiniteHole Vc) :
-- imply
  kc14_NoSecondBoundedRegion Vc := by
-- proof
  apply StatMech.Walls.kc14_noSecondBoundedRegion_of_noFiniteHole Vc hres

/--
[kc14_noSecondBoundedRegion_iff_noFiniteHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_noSecondBoundedRegion_iff_noFiniteHole_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  kc14_NoSecondBoundedRegion Vc ↔ kc13_NoFiniteHole Vc := by
-- proof
  apply StatMech.Walls.kc14_noSecondBoundedRegion_iff_noFiniteHole Vc

/--
[kc14_reachesFarLeftBeacon_of_noSecondBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_reachesFarLeftBeacon_of_noSecondBoundedRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hres : kc14_NoSecondBoundedRegion Vc) :
-- imply
  kc12_ReachesFarLeftBeacon Vc R := by
-- proof
  apply StatMech.Walls.kc14_reachesFarLeftBeacon_of_noSecondBoundedRegion Vc R hsupp hres

/--
[kc14_offSupportOutsideInfinite_of_noSecondBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_offSupportOutsideInfinite_of_noSecondBoundedRegion_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hres : kc14_NoSecondBoundedRegion (mpl_orbitLoop K a)) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc14_offSupportOutsideInfinite_of_noSecondBoundedRegion K a R hRbox hbridge hres

/--
[kc14_unitCell_noSecondBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_unitCell_noSecondBoundedRegion_eq
  {a : Site 2} :
-- imply
  kc14_NoSecondBoundedRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc14_unitCell_noSecondBoundedRegion

/--
[kc14_unitCell_reachesFarLeftBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_unitCell_reachesFarLeftBeacon_eq
  {a : Site 2} :
-- imply
  kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc14_unitCell_reachesFarLeftBeacon

/--
[kc14_unitCell_no_finite_outside_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean)
-/
@[path]
private lemma kc14_unitCell_no_finite_outside_component_eq
  {a : Site 2}
  {z : Site 2}
-- given
  (hz : z ∉ (mpl_orbitLoop unitCell ucBase).support)
  (hzout : z ∉ jec_leftRegion (mpl_orbitLoop unitCell ucBase)) :
-- imply
  ¬ (kc12_component (mpl_orbitLoop unitCell ucBase) z).Finite := by
-- proof
  apply StatMech.Walls.kc14_unitCell_no_finite_outside_component z hz hzout


-- created on 2026-10-23
