import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[oc_mem_supportSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_mem_supportSet_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ oc_supportSet Vc ↔ z ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_mem_supportSet Vc z

/--
[oc_offSupportLattice_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_offSupportLattice_reachable_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y ↔ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_offSupportLattice_reachable_iff Vc hx

/--
[oc_exterior_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_exterior_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_exterior_offSupport Vc R hsupp hz

/--
[oc_exterior_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_exterior_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.oc_exterior_outside Vc R hsupp hz

/--
[oc_exterior_adj_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_exterior_adj_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R)
  (hadj : (hypercubicLattice 2).Adj x y) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Adj x y := by
-- proof
  apply StatMech.Lattice.oc_exterior_adj_offSupport Vc R hsupp hx hy hadj

/--
[oc_exterior_reachable_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_exterior_reachable_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.oc_exterior_reachable_offSupport Vc R hsupp hx hy

/--
[oc_farExterior_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_farExterior_offSupport_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_farExterior_offSupport_walk Vc R hsupp hx hy

/--
[oc_hOutOff_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_hOutOff_of_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : oc_OutsideReachesExterior Vc R) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_hOutOff_of_reachesExterior Vc R hsupp h

/--
[oc_two_components_of_outsideReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_two_components_of_outsideReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hOut : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.oc_two_components_of_outsideReaches Vc R hsupp hp hq hInOff hOut

/--
[oc_exterior_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_exterior_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_exterior_reachesExterior Vc R hz

/--
[oc_mem_exterior_of_row_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_mem_exterior_of_row_high_eq
  {a : Site 2}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : (R : ℤ) + 1 ≤ z 1) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.oc_mem_exterior_of_row_high R hz

/--
[oc_mem_exterior_of_col_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_mem_exterior_of_col_high_eq
  {a : Site 2}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : (R : ℤ) + 1 ≤ z 0) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.oc_mem_exterior_of_col_high R hz

/--
[oc_reachesExterior_of_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_offSupport_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z e : Site 2}
  {p : (hypercubicLattice 2).Walk z e}
-- given
  (heExt : e ∈ exterior 2 R)
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  ∃ e' : Site 2, e' ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e' := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_offSupport_walk Vc R heExt p hp

/--
[oc_vertUpEscape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_vertUpEscape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ ∃ p : (hypercubicLattice 2).Walk z e, ∀ w ∈ p.support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_vertUpEscape Vc R hclear

/--
[oc_reachesExterior_of_vertUpClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_vertUpClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_vertUpClear Vc R hclear

/--
[oc_horizRightEscape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_horizRightEscape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ ∃ p : (hypercubicLattice 2).Walk z e, ∀ w ∈ p.support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_horizRightEscape Vc R hclear

/--
[oc_reachesExterior_of_horizRightClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_horizRightClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_horizRightClear Vc R hclear

/--
[oc_mem_exterior_of_row_low](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_mem_exterior_of_row_low_eq
  {a : Site 2}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : z 1 ≤ -((R : ℤ) + 1)) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.oc_mem_exterior_of_row_low R hz

/--
[oc_mem_exterior_of_col_low](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_mem_exterior_of_col_low_eq
  {a : Site 2}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : z 0 ≤ -((R : ℤ) + 1)) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.oc_mem_exterior_of_col_low R hz

/--
[oc_reachesExterior_of_vertDownClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_vertDownClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_vertDownClear Vc R hclear

/--
[oc_reachesExterior_of_horizLeftClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_horizLeftClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_horizLeftClear Vc R hclear

/--
[oc_vertUp_support_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_vertUp_support_col_eq
  {a : Site 2}
  {z : Site 2}
  {R : ℕ}
  {w : Site 2}
-- given
  (hw : w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support) :
-- imply
  ∃ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) ∧ w = ![z 0, t] := by
-- proof
  apply StatMech.Lattice.oc_vertUp_support_col hw

/--
[oc_vertUp_clear_of_colClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_vertUp_clear_of_colClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_vertUp_clear_of_colClear Vc R hcol

/--
[oc_reachesExterior_of_colClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_colClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_colClear Vc R hcol

/--
[oc_reachesExterior_of_row_ge_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_reachesExterior_of_row_ge_R_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzrow : (R : ℤ) ≤ z 1)
  (hzoff : z ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.oc_reachesExterior_of_row_ge_R Vc R hsupp hzrow hzoff

/--
[oc_outsideReachesExterior_of_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_outsideReachesExterior_of_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : oc_OutsideReachesTop Vc R) :
-- imply
  oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Lattice.oc_outsideReachesExterior_of_reachesTop Vc R hsupp h

/--
[oc_hOutOff_of_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_hOutOff_of_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : oc_OutsideReachesTop Vc R) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_hOutOff_of_reachesTop Vc R hsupp h

/--
[oc_two_components_of_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_two_components_of_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hTop : oc_OutsideReachesTop Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.oc_two_components_of_reachesTop Vc R hsupp hp hq hInOff hTop

/--
[oc_top_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_top_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hzrow : (R : ℤ) ≤ z 1)
  (hzoff : z ∉ Vc.support) :
-- imply
  ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧ ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_top_reachesTop Vc R hzrow hzoff

/--
[oc_colClear_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_colClear_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧ ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.oc_colClear_reachesTop Vc R hcol

/--
[oc_outsideReachesTop_of_outsideColClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean)
-/
@[path]
private lemma oc_outsideReachesTop_of_outsideColClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hall : ∀ z : Site 2, z ∉ jec_leftRegion Vc → ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  oc_OutsideReachesTop Vc R := by
-- proof
  apply StatMech.Lattice.oc_outsideReachesTop_of_outsideColClear Vc R hall


-- created on 2026-10-23
