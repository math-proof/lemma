import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.CriticalPoint
open MeasureTheory StatMech StatMech.FK


/--
[fkTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean)
-/
@[path]
private lemma fkTheta_nonneg_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ fkTheta d hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.fkTheta_nonneg d hp hp1 hq

/--
[fkTheta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean)
-/
@[path]
private lemma fkTheta_le_one_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkTheta d hp hp1 hq (q := q) ≤ 1 := by
-- proof
  apply StatMech.FK.fkTheta_le_one d hp hp1 hq

/--
[mem_fkSubcriticalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean)
-/
@[path]
private lemma mem_fkSubcriticalSet_eq
  {d : ℕ}
  {q : ℝ}
  {p : ℝ} :
-- imply
  p ∈ fkSubcriticalSet d q ↔ ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0 := by
-- proof
  apply StatMech.FK.mem_fkSubcriticalSet


-- created on 2026-10-23
