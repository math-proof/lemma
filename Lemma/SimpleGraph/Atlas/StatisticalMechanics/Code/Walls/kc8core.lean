import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc8core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc8_infinite_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_infinite_of_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
  {e : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzoff : z ∉ Vc.support)
  (heExt : e ∈ exterior 2 R)
  (hreach : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
-- imply
  ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ, (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc8_infinite_of_reachesExterior Vc R hsupp hzoff heExt hreach

/--
[kc8_outsideOffSupportInfinite_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_outsideOffSupportInfinite_of_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hEsc : kc5_OffSupportReachesExterior Vc R) :
-- imply
  kc5_OutsideOffSupportInfinite Vc := by
-- proof
  apply StatMech.Walls.kc8_outsideOffSupportInfinite_of_offSupportReaches Vc R hsupp hEsc

/--
[kc8_offSupportOutsideInfinite_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_offSupportOutsideInfinite_of_offSupportReaches_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hEsc : kc5_OffSupportReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc8_offSupportOutsideInfinite_of_offSupportReaches K a R hRbox hbridge hEsc

/--
[kc8_offSupportReaches_of_anyClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_offSupportReaches_of_anyClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hall : ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc → (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc8_offSupportReaches_of_anyClear Vc R hall

/--
[kc8_outsideOffSupportInfinite_of_anyClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_outsideOffSupportInfinite_of_anyClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hall : ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc → (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
-- imply
  kc5_OutsideOffSupportInfinite Vc := by
-- proof
  apply StatMech.Walls.kc8_outsideOffSupportInfinite_of_anyClear Vc R hsupp hall

/--
[kc8_unitCell_support_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_support_coords_eq
  {a : Site 2}
  {z : Site 2}
-- given
  (hz : z ∈ (mpl_orbitLoop unitCell ucBase).support) :
-- imply
  (z 0 = -1 ∨ z 0 = 0) ∧ (z 1 = -1 ∨ z 1 = 0) := by
-- proof
  apply StatMech.Walls.kc8_unitCell_support_coords z hz

/--
[kc8_unitCell_supp_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_supp_box_eq
  {a : Site 2} :
-- imply
  oc_supportSet (mpl_orbitLoop unitCell ucBase) ⊆ box 2 1 := by
-- proof
  apply StatMech.Walls.kc8_unitCell_supp_box

/--
[kc8_unitCell_coords_in_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_coords_in_support_eq
  {a : Site 2}
  {z : Site 2}
-- given
  (hc0 : z 0 = -1 ∨ z 0 = 0)
  (hc1 : z 1 = -1 ∨ z 1 = 0) :
-- imply
  z ∈ (mpl_orbitLoop unitCell ucBase).support := by
-- proof
  apply StatMech.Walls.kc8_unitCell_coords_in_support z hc0 hc1

/--
[kc8_unitCell_anyClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_anyClear_eq
  {a : Site 2}
  {z : Site 2}
-- given
  (hz : z ∉ (mpl_orbitLoop unitCell ucBase).support) :
-- imply
  (∀ w ∈ (sw_vertSeg (z 0) (z 1) (((1 : ℕ) : ℤ) + 1)).support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-(((1 : ℕ) : ℤ) + 1))).support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) (((1 : ℕ) : ℤ) + 1)).support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-(((1 : ℕ) : ℤ) + 1))).support, w ∉ (mpl_orbitLoop unitCell ucBase).support) := by
-- proof
  apply StatMech.Walls.kc8_unitCell_anyClear z hz

/--
[kc8_unitCell_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_offSupportReaches_eq
  {a : Site 2} :
-- imply
  kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc8_unitCell_offSupportReaches

/--
[kc8_unitCell_outsideOffSupportInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_outsideOffSupportInfinite_eq
  {a : Site 2} :
-- imply
  kc5_OutsideOffSupportInfinite (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc8_unitCell_outsideOffSupportInfinite

/--
[kc8_unitCell_offSupportOutsideInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_unitCell_offSupportOutsideInfinite_eq
  {a : Site 2} :
-- imply
  kc7_OffSupportOutsideInfinite unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc8_unitCell_offSupportOutsideInfinite

/--
[kc8_exterior_satisfies_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc8core.lean)
-/
@[path]
private lemma kc8_exterior_satisfies_escape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Walls.kc8_exterior_satisfies_escape Vc hz


-- created on 2026-10-23
