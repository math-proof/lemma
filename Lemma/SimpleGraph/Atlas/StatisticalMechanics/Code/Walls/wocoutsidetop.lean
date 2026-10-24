import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wocoutsidetop
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[woc_offSupport_eq_ffc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_offSupport_eq_ffc_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  offSupport Vc = ffc_offSupportLattice (oc_supportSet Vc) := by
-- proof
  apply StatMech.Lattice.woc_offSupport_eq_ffc Vc

/--
[woc_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_reachable_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2} :
-- imply
  (offSupport Vc).Reachable x y ↔ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.woc_reachable_iff Vc

/--
[woc_beacon_row_ge_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_beacon_row_ge_R_eq
  {a : Site 2}
  {R : ℕ} :
-- imply
  (R : ℤ) ≤ (beacon 2 R) 1 := by
-- proof
  apply StatMech.Lattice.woc_beacon_row_ge_R R

/--
[woc_beacon_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_beacon_mem_exterior_eq
  {a : Site 2}
  {R : ℕ} :
-- imply
  beacon 2 R ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.woc_beacon_mem_exterior R

/--
[woc_exterior_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_exterior_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {e : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (he : e ∈ exterior 2 R) :
-- imply
  ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable e w := by
-- proof
  apply StatMech.Lattice.woc_exterior_reachesTop Vc R hsupp he

/--
[woc_reachesExterior_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_reachesExterior_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z e : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzoff : z ∉ Vc.support)
  (he : e ∈ exterior 2 R)
  (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
-- imply
  ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧ ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.woc_reachesExterior_reachesTop Vc R hsupp hzoff he hze

/--
[woc_reachesTop_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_reachesTop_of_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : oc_OutsideReachesExterior Vc R) :
-- imply
  oc_OutsideReachesTop Vc R := by
-- proof
  apply StatMech.Lattice.woc_reachesTop_of_reachesExterior Vc R hsupp h

/--
[woc_reachesTop_iff_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_reachesTop_iff_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  oc_OutsideReachesTop Vc R ↔ oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Lattice.woc_reachesTop_iff_reachesExterior Vc R hsupp

/--
[woc_infiniteComponent_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_infiniteComponent_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z e : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hzoff : z ∉ Vc.support)
  (he : e ∈ exterior 2 R)
  (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.woc_infiniteComponent_outside Vc R hsupp hzoff he hze

/--
[woc_interiorComponent_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_interiorComponent_bounded_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {seed : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hseed : seed ∈ jec_leftRegion Vc)
  (hsoff : seed ∉ Vc.support) :
-- imply
  (offSupportComponent Vc seed).Finite := by
-- proof
  apply StatMech.Lattice.woc_interiorComponent_bounded Vc R hsupp hseed hsoff

/--
[woc_interior_not_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_interior_not_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hzin : z ∈ jec_leftRegion Vc)
  (hzoff : z ∉ Vc.support) :
-- imply
  ¬ ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.woc_interior_not_reachesExterior Vc R hsupp hzin hzoff

/--
[woc_residue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_residue_eq_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ} :
-- imply
  woc_OutsideReachesExterior_residue Vc R ↔ oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Lattice.woc_residue_eq Vc R

/--
[woc_reachesTop_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_reachesTop_of_residue_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : woc_OutsideReachesExterior_residue Vc R) :
-- imply
  oc_OutsideReachesTop Vc R := by
-- proof
  apply StatMech.Lattice.woc_reachesTop_of_residue Vc R hsupp h

/--
[woc_residue_iff_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_residue_iff_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  woc_OutsideReachesExterior_residue Vc R ↔ oc_OutsideReachesTop Vc R := by
-- proof
  apply StatMech.Lattice.woc_residue_iff_reachesTop Vc R hsupp

/--
[woc_component_has_lexMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_component_has_lexMax_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hfin : (offSupportComponent Vc seed).Finite) :
-- imply
  ∃ m ∈ offSupportComponent Vc seed, ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m := by
-- proof
  apply StatMech.Lattice.woc_component_has_lexMax Vc hfin

/--
[woc_up_not_mem_of_lexMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_up_not_mem_of_lexMax_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed m : Site 2}
-- given
  (hmax : ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m) :
-- imply
  (![m 0, m 1 + 1] : Site 2) ∉ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.woc_up_not_mem_of_lexMax Vc hmax

/--
[woc_extreme_up_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_extreme_up_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed m : Site 2}
-- given
  (hsoff : seed ∉ Vc.support)
  (hm : m ∈ offSupportComponent Vc seed)
  (hmax : ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m) :
-- imply
  (![m 0, m 1 + 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.woc_extreme_up_onSupport Vc hsoff hm hmax

/--
[woc_infinite_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_infinite_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (_hzoff : z ∉ Vc.support)
  (hinf : (offSupportComponent Vc z).Infinite) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.woc_infinite_reachesExterior Vc R _hzoff hinf

/--
[woc_residue_of_noBoundedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_residue_of_noBoundedEven_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
  (h : woc_NoBoundedEvenComponent Vc) :
-- imply
  woc_OutsideReachesExterior_residue Vc R := by
-- proof
  apply StatMech.Lattice.woc_residue_of_noBoundedEven Vc R hoffOut h

/--
[woc_reachesTop_of_noBoundedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_reachesTop_of_noBoundedEven_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
  (h : woc_NoBoundedEvenComponent Vc) :
-- imply
  oc_OutsideReachesTop Vc R := by
-- proof
  apply StatMech.Lattice.woc_reachesTop_of_noBoundedEven Vc R hsupp hoffOut h

/--
[woc_two_components_of_noBoundedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_two_components_of_noBoundedEven_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
  (h : woc_NoBoundedEvenComponent Vc) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.woc_two_components_of_noBoundedEven Vc R hsupp hp hq hInOff hoffOut h

/--
[woc_interior_satisfies_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean)
-/
@[path]
private lemma woc_interior_satisfies_residue_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hzin : z ∈ jec_leftRegion Vc)
  (hzoff : z ∉ Vc.support) :
-- imply
  (offSupportComponent Vc z).Finite ∧ z ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.woc_interior_satisfies_residue Vc R hsupp hzin hzoff


-- created on 2026-10-23
