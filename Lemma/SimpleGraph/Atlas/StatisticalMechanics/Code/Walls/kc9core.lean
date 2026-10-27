import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc9core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc9_offSupportReaches_of_rightStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_offSupportReaches_of_rightStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hstep : ecc_RightStep Vc R) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc9_offSupportReaches_of_rightStep Vc R hstep

/--
[kc9_offSupportReaches_of_rightDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_offSupportReaches_of_rightDodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hdodge : ecc_RightDodge Vc R) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc9_offSupportReaches_of_rightDodge Vc R hdodge

/--
[kc9_outsideOffSupportInfinite_of_rightDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_outsideOffSupportInfinite_of_rightDodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hdodge : ecc_RightDodge Vc R) :
-- imply
  kc5_OutsideOffSupportInfinite Vc := by
-- proof
  apply StatMech.Walls.kc9_outsideOffSupportInfinite_of_rightDodge Vc R hsupp hdodge

/--
[kc9_offSupportOutsideInfinite_of_rightDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_offSupportOutsideInfinite_of_rightDodge_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hdodge : ecc_RightDodge (mpl_orbitLoop K a) R) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc9_offSupportOutsideInfinite_of_rightDodge K a R hRbox hbridge hdodge

/--
[kc9_upStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_upStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hupOff : (![z 0, z 1 + 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z ![z 0, z 1 + 1] := by
-- proof
  apply StatMech.Walls.kc9_upStep Vc hzoff hupOff

/--
[kc9_downStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_downStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hdownOff : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z ![z 0, z 1 - 1] := by
-- proof
  apply StatMech.Walls.kc9_downStep Vc hzoff hdownOff

/--
[kc9_overTop_dodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_overTop_dodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hupOff : (![z 0, z 1 + 1] : Site 2) ∉ Vc.support)
  (hupRightOff : (![z 0 + 1, z 1 + 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
-- proof
  apply StatMech.Walls.kc9_overTop_dodge Vc hzoff hupOff hupRightOff

/--
[kc9_underBottom_dodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_underBottom_dodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hdownOff : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support)
  (hdownRightOff : (![z 0 + 1, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
-- proof
  apply StatMech.Walls.kc9_underBottom_dodge Vc hzoff hdownOff hdownRightOff

/--
[kc9_rightStep_of_localDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_rightStep_of_localDodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hloc : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) → (![z 0 + 1, z 1] : Site 2) ∉ Vc.support ∨ ((![z 0, z 1 + 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 + 1] : Site 2) ∉ Vc.support) ∨ ((![z 0, z 1 - 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 - 1] : Site 2) ∉ Vc.support)) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Walls.kc9_rightStep_of_localDodge Vc R hloc

/--
[kc9_offSupportReaches_of_localDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_offSupportReaches_of_localDodge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hloc : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) → (![z 0 + 1, z 1] : Site 2) ∉ Vc.support ∨ ((![z 0, z 1 + 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 + 1] : Site 2) ∉ Vc.support) ∨ ((![z 0, z 1 - 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 - 1] : Site 2) ∉ Vc.support)) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc9_offSupportReaches_of_localDodge Vc R hloc

/--
[kc9_rightStep_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_rightStep_of_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior Vc R) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Walls.kc9_rightStep_of_offSupportReaches Vc R hsupp hesc

/--
[kc9_rightDodge_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_rightDodge_of_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior Vc R) :
-- imply
  ecc_RightDodge Vc R := by
-- proof
  apply StatMech.Walls.kc9_rightDodge_of_offSupportReaches Vc R hsupp hesc

/--
[kc9_offSupportReaches_iff_rightStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_offSupportReaches_iff_rightStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  kc5_OffSupportReachesExterior Vc R ↔ ecc_RightStep Vc R := by
-- proof
  apply StatMech.Walls.kc9_offSupportReaches_iff_rightStep Vc R hsupp

/--
[kc9_unitCell_rightDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_unitCell_rightDodge_eq
  {a : Site 2} :
-- imply
  ecc_RightDodge (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc9_unitCell_rightDodge

/--
[kc9_unitCell_offSupportReaches_via_dodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_unitCell_offSupportReaches_via_dodge_eq
  {a : Site 2} :
-- imply
  kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc9_unitCell_offSupportReaches_via_dodge

/--
[kc9_unitCell_outsideOffSupportInfinite_via_dodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc9core.lean)
-/
@[path]
private lemma kc9_unitCell_outsideOffSupportInfinite_via_dodge_eq
  {a : Site 2} :
-- imply
  kc5_OutsideOffSupportInfinite (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc9_unitCell_outsideOffSupportInfinite_via_dodge


-- created on 2026-10-23
