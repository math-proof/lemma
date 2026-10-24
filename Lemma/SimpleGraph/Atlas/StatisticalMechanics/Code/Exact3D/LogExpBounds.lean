import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.LogExpBounds
open StatMech StatMech.Exact3D StatMech.Exact3D.ExpUpperBound StatMech.Exact3D.LogUpperBound StatMech.Exact3D.LogLowerBound


/--
[expUpperBound_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma expUpperBound_iff_eq
  {q r : ℝ} :
-- imply
  ExpUpperBound q r ↔ Real.exp q ≤ r := by
-- proof
  apply StatMech.Exact3D.expUpperBound_iff

/--
[logUpperBound_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma logUpperBound_iff_eq
  {x u : ℝ} :
-- imply
  LogUpperBound x u ↔ 0 < x ∧ Real.log x ≤ u := by
-- proof
  apply StatMech.Exact3D.logUpperBound_iff

/--
[logLowerBound_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma logLowerBound_iff_eq
  {l x : ℝ} :
-- imply
  LogLowerBound l x ↔ 0 < x ∧ l ≤ Real.log x := by
-- proof
  apply StatMech.Exact3D.logLowerBound_iff

/--
[log_le_of_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma log_le_of_le_exp_eq
  {x u : ℝ}
-- given
  (hx : 0 < x)
  (hxu : x ≤ Real.exp u) :
-- imply
  Real.log x ≤ u := by
-- proof
  apply StatMech.Exact3D.log_le_of_le_exp hx hxu

/--
[le_exp_of_log_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma le_exp_of_log_le_eq
  {x u : ℝ}
-- given
  (hx : 0 < x)
  (hxu : Real.log x ≤ u) :
-- imply
  x ≤ Real.exp u := by
-- proof
  apply StatMech.Exact3D.le_exp_of_log_le hx hxu

/--
[le_log_of_exp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma le_log_of_exp_le_eq
  {l x : ℝ}
-- given
  (hlx : Real.exp l ≤ x) :
-- imply
  l ≤ Real.log x := by
-- proof
  apply StatMech.Exact3D.le_log_of_exp_le hlx

/--
[exp_le_of_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma exp_le_of_le_log_eq
  {l x : ℝ}
-- given
  (hx : 0 < x)
  (hlx : l ≤ Real.log x) :
-- imply
  Real.exp l ≤ x := by
-- proof
  apply StatMech.Exact3D.exp_le_of_le_log hx hlx

/--
[log_le_of_le_of_log_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma log_le_of_le_of_log_le_eq
  {x y u : ℝ}
-- given
  (hx : 0 < x)
  (hxy : x ≤ y)
  (hyu : Real.log y ≤ u) :
-- imply
  Real.log x ≤ u := by
-- proof
  apply StatMech.Exact3D.log_le_of_le_of_log_le hx hxy hyu

/--
[le_log_of_le_of_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma le_log_of_le_of_le_log_eq
  {l x y : ℝ}
-- given
  (hx : 0 < x)
  (hxy : x ≤ y)
  (hlx : l ≤ Real.log x) :
-- imply
  l ≤ Real.log y := by
-- proof
  apply StatMech.Exact3D.le_log_of_le_of_le_log hx hxy hlx

/--
[rhs_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma rhs_pos_eq
  {q r : ℝ}
-- given
  (h : ExpUpperBound q r) :
-- imply
  0 < r := by
-- proof
  apply StatMech.Exact3D.ExpUpperBound.rhs_pos h

/--
[rhs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma rhs_nonneg_eq
  {q r : ℝ}
-- given
  (h : ExpUpperBound q r) :
-- imply
  0 ≤ r := by
-- proof
  apply StatMech.Exact3D.ExpUpperBound.rhs_nonneg h

/--
[mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma mono_left_eq
  {p q r : ℝ}
-- given
  (hpq : p ≤ q)
  (h : ExpUpperBound q r) :
-- imply
  ExpUpperBound p r where bound := by
-- proof
  apply StatMech.Exact3D.ExpUpperBound.mono_left hpq h

/--
[trans_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma trans_right_eq
  {q r s : ℝ}
-- given
  (h : ExpUpperBound q r)
  (hrs : r ≤ s) :
-- imply
  ExpUpperBound q s where bound := by
-- proof
  apply StatMech.Exact3D.ExpUpperBound.trans_right h hrs

/--
[toLogLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma toLogLowerBound_eq
  {q r : ℝ}
-- given
  (h : ExpUpperBound q r) :
-- imply
  LogLowerBound q r where x_pos := by
-- proof
  apply StatMech.Exact3D.ExpUpperBound.toLogLowerBound h

/--
[mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma mono_left_eq_2
  {x y u : ℝ}
-- given
  (hy : 0 < y)
  (hyx : y ≤ x)
  (h : LogUpperBound x u) :
-- imply
  LogUpperBound y u where x_pos := by
-- proof
  apply StatMech.Exact3D.LogUpperBound.mono_left hy hyx h

/--
[trans_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma trans_right_eq_2
  {x u v : ℝ}
-- given
  (h : LogUpperBound x u)
  (huv : u ≤ v) :
-- imply
  LogUpperBound x v where x_pos := by
-- proof
  apply StatMech.Exact3D.LogUpperBound.trans_right h huv

/--
[le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma le_exp_eq
  {x u : ℝ}
-- given
  (h : LogUpperBound x u) :
-- imply
  x ≤ Real.exp u := by
-- proof
  apply StatMech.Exact3D.LogUpperBound.le_exp h

/--
[of_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma of_le_exp_eq
  {x u : ℝ}
-- given
  (hx : 0 < x)
  (hxu : x ≤ Real.exp u) :
-- imply
  LogUpperBound x u where x_pos := by
-- proof
  apply StatMech.Exact3D.LogUpperBound.of_le_exp hx hxu

/--
[trans_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma trans_left_eq
  {k l x : ℝ}
-- given
  (hkl : k ≤ l)
  (h : LogLowerBound l x) :
-- imply
  LogLowerBound k x where x_pos := by
-- proof
  apply StatMech.Exact3D.LogLowerBound.trans_left hkl h

/--
[mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma mono_right_eq
  {l x y : ℝ}
-- given
  (h : LogLowerBound l x)
  (hxy : x ≤ y) :
-- imply
  LogLowerBound l y where x_pos := by
-- proof
  apply StatMech.Exact3D.LogLowerBound.mono_right h hxy

/--
[exp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma exp_le_eq
  {l x : ℝ}
-- given
  (h : LogLowerBound l x) :
-- imply
  Real.exp l ≤ x := by
-- proof
  apply StatMech.Exact3D.LogLowerBound.exp_le h

/--
[of_exp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma of_exp_le_eq
  {l x : ℝ}
-- given
  (hlx : Real.exp l ≤ x) :
-- imply
  LogLowerBound l x where x_pos := by
-- proof
  apply StatMech.Exact3D.LogLowerBound.of_exp_le hlx

/--
[toExpUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma toExpUpperBound_eq
  {l x : ℝ}
-- given
  (h : LogLowerBound l x) :
-- imply
  ExpUpperBound l x where bound := by
-- proof
  apply StatMech.Exact3D.LogLowerBound.toExpUpperBound h

/--
[expUpperBound_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma expUpperBound_zero_one_eq :
-- imply
  ExpUpperBound 0 1 where bound := by
-- proof
  apply StatMech.Exact3D.expUpperBound_zero_one

/--
[logUpperBound_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma logUpperBound_one_zero_eq :
-- imply
  LogUpperBound 1 0 where x_pos := by
-- proof
  apply StatMech.Exact3D.logUpperBound_one_zero

/--
[logLowerBound_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean)
-/
@[path]
private lemma logLowerBound_zero_one_eq :
-- imply
  LogLowerBound 0 1 where x_pos := by
-- proof
  apply StatMech.Exact3D.logLowerBound_zero_one


-- created on 2026-10-23
