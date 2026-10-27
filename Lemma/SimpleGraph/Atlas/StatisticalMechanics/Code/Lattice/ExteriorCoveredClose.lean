import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorCoveredClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ecc_reach_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_reach_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z w : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (h : (offSupport Vc).Reachable z w) :
-- imply
  w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.ecc_reach_offSupport Vc hzoff h

/--
[ecc_reaches_right_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_reaches_right_band_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hstep : ecc_RightStep Vc R)
  (hzout : z ∉ jec_leftRegion Vc)
  (hzoff : z ∉ Vc.support) :
-- imply
  ∃ w : Site 2, (R : ℤ) + 1 ≤ w 0 ∧ (offSupport Vc).Reachable z w := by
-- proof
  apply StatMech.Lattice.ecc_reaches_right_band Vc R hstep z hzout hzoff

/--
[ecc_outsideReachesExterior_of_rightStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_outsideReachesExterior_of_rightStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
  (hstep : ecc_RightStep Vc R) :
-- imply
  oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Lattice.ecc_outsideReachesExterior_of_rightStep Vc R hoffOut hstep

/--
[ecc_exteriorCovered_of_rightStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_exteriorCovered_of_rightStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
  (hbExt : beacon ∈ exterior 2 R)
  (hstep : ecc_RightStep Vc R) :
-- imply
  orc_ExteriorCovered Vc beacon := by
-- proof
  apply StatMech.Lattice.ecc_exteriorCovered_of_rightStep Vc R hsupp hoffOut hbExt hstep

/--
[ecc_two_components_of_rightStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_two_components_of_rightStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
  (hstep : ecc_RightStep Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ecc_two_components_of_rightStep Vc R hsupp hp hq hInOff hoffOut hstep

/--
[ecc_rightNeighbor_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_rightNeighbor_step_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hnbOff : (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z ![z 0 + 1, z 1] := by
-- proof
  apply StatMech.Lattice.ecc_rightNeighbor_step Vc hzoff hnbOff

/--
[ecc_rightStep_of_rightDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_rightStep_of_rightDodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hdodge : ecc_RightDodge Vc R) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Lattice.ecc_rightStep_of_rightDodge Vc R hdodge

/--
[ecc_rightStep_of_rightNeighbor_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_rightStep_of_rightNeighbor_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hnb : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) → (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Lattice.ecc_rightStep_of_rightNeighbor_offSupport Vc R hnb

/--
[ecc_rightStep_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_rightStep_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hflood : oc_OutsideReachesExterior Vc R) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Lattice.ecc_rightStep_of_floodFill Vc R hsupp hflood

/--
[ecc_rightStep_iff_exteriorCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean)
-/
@[path]
private lemma ecc_rightStep_iff_exteriorCovered_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {beacon : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
  (hbExt : beacon ∈ exterior 2 R)
  (hbOff : beacon ∉ Vc.support) :
-- imply
  ecc_RightStep Vc R ↔ orc_ExteriorCovered Vc beacon := by
-- proof
  apply StatMech.Lattice.ecc_rightStep_iff_exteriorCovered Vc R hsupp hoffOut hbExt hbOff


-- created on 2026-10-23
