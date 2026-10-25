import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OutsideCoveringClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ocov_beacon_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beacon_mem_exterior_eq
  {a : Site 2}
  {R : ℕ} :
-- imply
  beacon 2 R ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.ocov_beacon_mem_exterior R

/--
[ocov_beacon_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beacon_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  beacon 2 R ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.ocov_beacon_offSupport Vc R hsupp

/--
[ocov_beacon_in_beaconFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beacon_in_beaconFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ} :
-- imply
  beacon 2 R ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_beacon_in_beaconFill Vc R

/--
[ocov_exterior_in_beaconFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_exterior_in_beaconFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_exterior_in_beaconFill Vc R hsupp hz

/--
[ocov_exterior_subset_beaconFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_exterior_subset_beaconFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  exterior 2 R ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_exterior_subset_beaconFill Vc R hsupp

/--
[ocov_in_beaconFill_of_reaches_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_in_beaconFill_of_reaches_exterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z e : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (he : e ∈ exterior 2 R)
  (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
-- imply
  z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_in_beaconFill_of_reaches_exterior Vc R hsupp he hze

/--
[ocov_row_ge_R_in_beaconFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_row_ge_R_in_beaconFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzrow : (R : ℤ) ≤ z 1)
  (hzoff : z ∉ Vc.support) :
-- imply
  z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_row_ge_R_in_beaconFill Vc R hsupp hzrow hzoff

/--
[ocov_beacon_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beacon_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  beacon 2 R ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ocov_beacon_outside Vc R hsupp

/--
[ocov_beaconFill_mem_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beaconFill_mem_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ocov_beaconFill_mem_outside Vc R hsupp hz

/--
[ocov_beaconFill_subset_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beaconFill_subset_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ⊆ (jec_leftRegion Vc)ᶜ := by
-- proof
  apply StatMech.Lattice.ocov_beaconFill_subset_outside Vc R hsupp

/--
[ocov_reachesExterior_of_in_beaconFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_reachesExterior_of_in_beaconFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.ocov_reachesExterior_of_in_beaconFill Vc R hz

/--
[ocov_reachesExterior_iff_in_beaconFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_reachesExterior_iff_in_beaconFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  (∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) ↔ z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_reachesExterior_iff_in_beaconFill Vc R hsupp

/--
[ocov_outsideReachesExterior_iff_beaconCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_outsideReachesExterior_iff_beaconCovers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  oc_OutsideReachesExterior Vc R ↔ (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_outsideReachesExterior_iff_beaconCovers Vc R hsupp

/--
[ocov_beaconFill_eq_outside_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beaconFill_eq_outside_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  ffc_floodFill (oc_supportSet Vc) (beacon 2 R) = (jec_leftRegion Vc)ᶜ ↔ (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_beaconFill_eq_outside_iff Vc R hsupp

/--
[ocov_hOutOff_of_beaconCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_hOutOff_of_beaconCovers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hcov : (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.ocov_hOutOff_of_beaconCovers Vc R hsupp hcov

/--
[ocov_two_components_of_beaconCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_two_components_of_beaconCovers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hcov : (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ocov_two_components_of_beaconCovers Vc R hsupp hp hq hInOff hcov

/--
[ocov_beaconFill_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beaconFill_nonvacuous_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  beacon 2 R ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ∧ exterior 2 R ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ∧ (∀ z : Site 2, (R : ℤ) ≤ z 1 → z ∉ Vc.support → z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) := by
-- proof
  apply StatMech.Lattice.ocov_beaconFill_nonvacuous Vc R hsupp

/--
[ocov_beaconCovers_of_outsideExteriorOrHigh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideCoveringClose.lean)
-/
@[path]
private lemma ocov_beaconCovers_of_outsideExteriorOrHigh_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hall : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∈ exterior 2 R ∨ ((R : ℤ) ≤ z 1 ∧ z ∉ Vc.support)) :
-- imply
  (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.ocov_beaconCovers_of_outsideExteriorOrHigh Vc R hsupp hall


-- created on 2026-10-23
