import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.FacialSurjectivityProve
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[fsp_canonicalCount_eq_componentCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_canonicalCount_eq_componentCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Nat.card (fsv_canonicalFamily Vc) = Nat.card (fcb_offComplGraph Vc).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.fsp_canonicalCount_eq_componentCount Vc

/--
[fsp_canonicalCount_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_canonicalCount_eq_two_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : fcb_OffComplJordanRegion Vc) :
-- imply
  Nat.card (fsv_canonicalFamily Vc) = 2 := by
-- proof
  apply StatMech.Lattice.fsp_canonicalCount_eq_two Vc h

/--
[fsp_canonicalCount_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_canonicalCount_eq_faceCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (h : fcb_OffComplJordanRegion Vc)
  (hc : c.IsCycle) :
-- imply
  Nat.card (fsv_canonicalFamily Vc) = faceCount c.toSubgraph.coe := by
-- proof
  apply StatMech.Lattice.fsp_canonicalCount_eq_faceCount Vc h c hc

/--
[fsp_offSupportComponent_inside_ne_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_offSupportComponent_inside_ne_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support) :
-- imply
  offSupportComponent Vc x ≠ offSupportComponent Vc y := by
-- proof
  apply StatMech.Lattice.fsp_offSupportComponent_inside_ne_outside Vc hxin hyout hyoff

/--
[fsp_inside_outside_facialOrbit_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_inside_outside_facialOrbit_ne_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support) :
-- imply
  {d : Dart | IsBoundaryDart (offSupportComponent Vc x) d} ≠ {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d} := by
-- proof
  apply StatMech.Lattice.fsp_inside_outside_facialOrbit_ne Vc hxin hxoff hyout hyoff

/--
[fsp_facialOrbit_has_incident_cell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_facialOrbit_has_incident_cell_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support) :
-- imply
  ∃ e : Dart, e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc z) d} ∧ e.tail ∈ offSupportComponent Vc z := by
-- proof
  apply StatMech.Lattice.fsp_facialOrbit_has_incident_cell Vc hz

/--
[fsp_offSupportComponent_eq_inside_or_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_offSupportComponent_eq_inside_or_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {z : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
  (hz : z ∉ Vc.support) :
-- imply
  offSupportComponent Vc z = offSupportComponent Vc x ∨ offSupportComponent Vc z = offSupportComponent Vc y := by
-- proof
  apply StatMech.Lattice.fsp_offSupportComponent_eq_inside_or_outside Vc hxin hxoff hyout hyoff hin hout hz

/--
[fsp_canonicalFamily_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_canonicalFamily_eq_pair_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  fsv_canonicalFamily Vc = {{d : Dart | IsBoundaryDart (offSupportComponent Vc x) d}, {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d}} := by
-- proof
  apply StatMech.Lattice.fsp_canonicalFamily_eq_pair Vc hxin hxoff hyout hyoff hin hout

/--
[fsp_canonicalFamily_eq_pair_of_jordanRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_canonicalFamily_eq_pair_of_jordanRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : fcb_OffComplJordanRegion Vc) :
-- imply
  ∃ x y : Site 2, x ∈ jec_leftRegion Vc ∧ x ∉ Vc.support ∧ y ∉ jec_leftRegion Vc ∧ y ∉ Vc.support ∧ fsv_canonicalFamily Vc = {{d : Dart | IsBoundaryDart (offSupportComponent Vc x) d}, {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d}} := by
-- proof
  apply StatMech.Lattice.fsp_canonicalFamily_eq_pair_of_jordanRegion Vc h

/--
[fsp_canonical_isPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivityProve.lean)
-/
@[path]
private lemma fsp_canonical_isPair_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  Nat.card (fsv_canonicalFamily Vc) = 2 := by
-- proof
  apply StatMech.Lattice.fsp_canonical_isPair Vc hxin hxoff hyout hyoff hin hout


-- created on 2026-10-23
