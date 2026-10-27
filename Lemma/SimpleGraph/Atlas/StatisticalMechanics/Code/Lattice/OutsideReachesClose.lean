import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OutsideReachesClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[orc_offSupportLattice_reachable_of_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_offSupportLattice_reachable_of_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support)
  (h : (offSupport Vc).Reachable x y) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.orc_offSupportLattice_reachable_of_offSupport Vc hx h

/--
[orc_offSupport_reachable_of_offSupportLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_offSupport_reachable_of_offSupportLattice_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support)
  (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y) :
-- imply
  (offSupport Vc).Reachable x y := by
-- proof
  apply StatMech.Lattice.orc_offSupport_reachable_of_offSupportLattice Vc hx h

/--
[orc_exteriorHub_of_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_exteriorHub_of_covered_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {beacon : Site 2}
-- given
  (hcov : orc_ExteriorCovered Vc beacon) :
-- imply
  ∀ s : Site 2, s ∉ jec_leftRegion Vc → (offSupport Vc).Reachable beacon s := by
-- proof
  apply StatMech.Lattice.orc_exteriorHub_of_covered Vc hcov

/--
[orc_outsideReachesExterior_of_exteriorCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_outsideReachesExterior_of_exteriorCovered_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hbExt : beacon ∈ exterior 2 R)
  (hbOff : beacon ∉ Vc.support)
  (hcov : orc_ExteriorCovered Vc beacon) :
-- imply
  oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Lattice.orc_outsideReachesExterior_of_exteriorCovered Vc R hbExt hbOff hcov

/--
[orc_exteriorCovered_of_outsideReachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_exteriorCovered_of_outsideReachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hbExt : beacon ∈ exterior 2 R)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  orc_ExteriorCovered Vc beacon := by
-- proof
  apply StatMech.Lattice.orc_exteriorCovered_of_outsideReachesExterior Vc R hsupp hbExt hFlood

/--
[orc_exteriorCovered_iff_outsideReachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_exteriorCovered_iff_outsideReachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hbExt : beacon ∈ exterior 2 R)
  (hbOff : beacon ∉ Vc.support) :
-- imply
  orc_ExteriorCovered Vc beacon ↔ oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Lattice.orc_exteriorCovered_iff_outsideReachesExterior Vc R hsupp hbExt hbOff

/--
[orc_reachesExterior_of_anyClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_reachesExterior_of_anyClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.orc_reachesExterior_of_anyClear Vc R hclear

/--
[orc_anyClear_inhabits_conclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_anyClear_inhabits_conclusion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.orc_anyClear_inhabits_conclusion Vc R hclear

/--
[orc_exteriorCovered_of_outside_eq_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_exteriorCovered_of_outside_eq_exterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hbExt : beacon ∈ exterior 2 R)
  (hbOff : beacon ∉ Vc.support)
  (hout : (jec_leftRegion Vc)ᶜ ⊆ exterior 2 R) :
-- imply
  orc_ExteriorCovered Vc beacon := by
-- proof
  apply StatMech.Lattice.orc_exteriorCovered_of_outside_eq_exterior Vc R hsupp hbExt hbOff hout

/--
[orc_hOutOff_of_exteriorCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_hOutOff_of_exteriorCovered_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hbExt : beacon ∈ exterior 2 R)
  (hbOff : beacon ∉ Vc.support)
  (hcov : orc_ExteriorCovered Vc beacon) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.orc_hOutOff_of_exteriorCovered Vc R hsupp hbExt hbOff hcov

/--
[orc_two_components_of_exteriorCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean)
-/
@[path]
private lemma orc_two_components_of_exteriorCovered_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hbExt : beacon ∈ exterior 2 R)
  (hbOff : beacon ∉ Vc.support)
  (hcov : orc_ExteriorCovered Vc beacon) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.orc_two_components_of_exteriorCovered Vc R hsupp hp hq hInOff hbExt hbOff hcov


-- created on 2026-10-23
