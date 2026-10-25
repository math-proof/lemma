import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc16wallfollow.Part3
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc16_climbUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_climbUp_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {k : ℕ}
-- given
  (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z ![z 0, z 1 + (k : ℤ)] := by
-- proof
  apply StatMech.Walls.kc16_climbUp Vc z k hoff

/--
[kc16_climbDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_climbDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {k : ℕ}
-- given
  (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z ![z 0, z 1 - (k : ℤ)] := by
-- proof
  apply StatMech.Walls.kc16_climbDown Vc z k hoff

/--
[kc16_climbUp_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_climbUp_step_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {k : ℕ}
-- given
  (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support)
  (hright : (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support) :
-- imply
  ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
-- proof
  apply StatMech.Walls.kc16_climbUp_step Vc z k hoff hright

/--
[kc16_climbDown_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_climbDown_step_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {k : ℕ}
-- given
  (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support)
  (hright : (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support) :
-- imply
  ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
-- proof
  apply StatMech.Walls.kc16_climbDown_step Vc z k hoff hright

/--
[kc16_rightDodge_of_verticalDetour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_rightDodge_of_verticalDetour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hdet : kc16_VerticalDetour Vc R) :
-- imply
  ecc_RightDodge Vc R := by
-- proof
  apply StatMech.Walls.kc16_rightDodge_of_verticalDetour Vc R hdet

/--
[kc16_offSupportReaches_of_verticalDetour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_offSupportReaches_of_verticalDetour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hdet : kc16_VerticalDetour Vc R) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc16_offSupportReaches_of_verticalDetour Vc R hdet

/--
[kc16_offSupport_of_row_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_offSupport_of_row_high_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {w : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hw : (R : ℤ) < w 1 ∨ w 1 < -(R : ℤ)) :
-- imply
  w ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc16_offSupport_of_row_high Vc R hsupp hw

/--
[kc16_detour_up_of_homeColumnClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_detour_up_of_homeColumnClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzrow : z 1 ≤ (R : ℤ))
  (hcol : ∀ j : ℕ, j ≤ ((R : ℤ) + 1 - z 1).toNat → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) :
-- imply
  ∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∧ (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc16_detour_up_of_homeColumnClear Vc R hsupp z hzrow hcol

/--
[kc16_detour_down_of_homeColumnClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_detour_down_of_homeColumnClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzrow : -(R : ℤ) ≤ z 1)
  (hcol : ∀ j : ℕ, j ≤ ((R : ℤ) + 1 + z 1).toNat → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) :
-- imply
  ∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) ∧ (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc16_detour_down_of_homeColumnClear Vc R hsupp z hzrow hcol

/--
[kc16_verticalDetour_of_clearEscapeColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_verticalDetour_of_clearEscapeColumn_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hcol : kc16_ClearEscapeColumn Vc R) :
-- imply
  kc16_VerticalDetour Vc R := by
-- proof
  apply StatMech.Walls.kc16_verticalDetour_of_clearEscapeColumn Vc R hsupp hcol

/--
[kc16_rightDodge_of_clearEscapeColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_rightDodge_of_clearEscapeColumn_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hcol : kc16_ClearEscapeColumn Vc R) :
-- imply
  ecc_RightDodge Vc R := by
-- proof
  apply StatMech.Walls.kc16_rightDodge_of_clearEscapeColumn Vc R hsupp hcol

/--
[kc16_offSupportReaches_of_clearEscapeColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_offSupportReaches_of_clearEscapeColumn_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hcol : kc16_ClearEscapeColumn Vc R) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc16_offSupportReaches_of_clearEscapeColumn Vc R hsupp hcol

/--
[kc16_offSupportOutsideInfinite_of_clearEscapeColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_offSupportOutsideInfinite_of_clearEscapeColumn_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hcol : kc16_ClearEscapeColumn (mpl_orbitLoop K a) R) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc16_offSupportOutsideInfinite_of_clearEscapeColumn K a R hRbox hbridge hcol

/--
[kc16_unitCell_clearEscapeColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_unitCell_clearEscapeColumn_eq
  {a : Site 2} :
-- imply
  kc16_ClearEscapeColumn (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc16_unitCell_clearEscapeColumn

/--
[kc16_unitCell_verticalDetour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_unitCell_verticalDetour_eq
  {a : Site 2} :
-- imply
  kc16_VerticalDetour (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc16_unitCell_verticalDetour

/--
[kc16_unitCell_rightDodge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_unitCell_rightDodge_eq
  {a : Site 2} :
-- imply
  ecc_RightDodge (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc16_unitCell_rightDodge

/--
[kc16_unitCell_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_unitCell_offSupportReaches_eq
  {a : Site 2} :
-- imply
  kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc16_unitCell_offSupportReaches

/--
[kc16_cappedColumn_no_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean)
-/
@[path]
private lemma kc16_cappedColumn_no_detour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hnb : (![z 0 + 1, z 1] : Site 2) ∈ Vc.support)
  (hup : (![z 0, z 1 + (1 : ℤ)] : Site 2) ∈ Vc.support)
  (hdown : (![z 0, z 1 - (1 : ℤ)] : Site 2) ∈ Vc.support) :
-- imply
  ¬ ((∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∧ (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support) ∨ (∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) ∧ (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support)) := by
-- proof
  apply StatMech.Walls.kc16_cappedColumn_no_detour Vc hnb hup hdown


-- created on 2026-10-23
