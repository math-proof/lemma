import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_topbandescape
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_mem_supportSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_mem_supportSet_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ kc4_supportSet Vc ↔ z ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_mem_supportSet Vc z

/--
[kc4_mem_exterior_of_row_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_mem_exterior_of_row_high_eq
  {a : Site 2}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : (R : ℤ) + 1 ≤ z 1) :
-- imply
  z ∈ exterior 2 R := by
-- proof
  apply StatMech.Walls.kc4_mem_exterior_of_row_high R hz

/--
[kc4_vertUp_support_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_vertUp_support_col_eq
  {a : Site 2}
  {z : Site 2}
  {R : ℕ}
  {w : Site 2}
-- given
  (hw : w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support) :
-- imply
  ∃ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) ∧ w = ![z 0, t] := by
-- proof
  apply StatMech.Walls.kc4_vertUp_support_col hw

/--
[kc4_vertUp_clear_of_colClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_vertUp_clear_of_colClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_vertUp_clear_of_colClear Vc R hcol

/--
[kc4_reachesExterior_of_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_reachesExterior_of_offSupport_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z e : Site 2}
  {p : (hypercubicLattice 2).Walk z e}
-- given
  (heExt : e ∈ exterior 2 R)
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  ∃ e' : Site 2, e' ∈ exterior 2 R ∧ (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e' := by
-- proof
  apply StatMech.Walls.kc4_reachesExterior_of_offSupport_walk Vc R heExt p hp

/--
[kc4_reachesExterior_of_colClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_reachesExterior_of_colClear_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Walls.kc4_reachesExterior_of_colClear Vc R hcol

/--
[kc4_TopBandEscape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_TopBandEscape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : kc4_supportSet Vc ⊆ box 2 R)
  (hzrow : (R : ℤ) ≤ z 1)
  (hzoff : z ∉ Vc.support) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Walls.kc4_TopBandEscape Vc R hsupp hzrow hzoff

/--
[kc4_topBand_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_topbandescape.lean)
-/
@[path]
private lemma kc4_topBand_self_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hzrow : (R : ℤ) + 1 ≤ z 1) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Walls.kc4_topBand_self Vc R hzrow


-- created on 2026-10-23
