import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.LogExpInterval.Part4
open StatMech StatMech.Exact3D StatMech.Exact3D.RatInterval


/--
[point_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma point_positive_eq
  {q : ℚ}
-- given
  (hq : 0 < q) :
-- imply
  (point q).Positive := by
-- proof
  apply StatMech.Exact3D.RatInterval.point_positive hq

/--
[lower_pos_real_of_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma lower_pos_real_of_positive_eq
  {I : RatInterval}
-- given
  (hI : I.Positive) :
-- imply
  (0 : ℝ) < (I.lower : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.lower_pos_real_of_positive hI

/--
[pos_of_positive_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma pos_of_positive_memR_eq
  {I : RatInterval}
  {x : ℝ}
-- given
  (hI : I.Positive)
  (hx : I.MemR x) :
-- imply
  0 < x := by
-- proof
  apply StatMech.Exact3D.RatInterval.pos_of_positive_memR hI hx

/--
[invPositive_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma invPositive_positive_eq
  {I : RatInterval}
-- given
  (hI : I.Positive) :
-- imply
  (invPositive I hI).Positive := by
-- proof
  apply StatMech.Exact3D.RatInterval.invPositive_positive hI

/--
[invPositive_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma invPositive_nonnegative_eq
  {I : RatInterval}
-- given
  (hI : I.Positive) :
-- imply
  (invPositive I hI).Nonnegative := by
-- proof
  apply StatMech.Exact3D.RatInterval.invPositive_nonnegative hI

/--
[invPositive_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma invPositive_memR_eq
  {I : RatInterval}
  {x : ℝ}
-- given
  (hI : I.Positive)
  (hx : I.MemR x) :
-- imply
  (invPositive I hI).MemR x⁻¹ := by
-- proof
  apply StatMech.Exact3D.RatInterval.invPositive_memR hI hx

/--
[divPositive_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma divPositive_memR_eq
  {I J : RatInterval}
  {x y : ℝ}
-- given
  (hJ : J.Positive)
  (hx : I.MemR x)
  (hy : J.MemR y) :
-- imply
  (divPositive I J hJ).MemR (x / y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.divPositive_memR hJ hx hy

/--
[divNonnegPositive_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma divNonnegPositive_memR_eq
  {I J : RatInterval}
  {x y : ℝ}
-- given
  (hI : I.Nonnegative)
  (hJ : J.Positive)
  (hx : I.MemR x)
  (hy : J.MemR y) :
-- imply
  (divNonnegPositive I J hI hJ).MemR (x / y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.divNonnegPositive_memR hI hJ hx hy

/--
[log_le_of_memR_upper_le_logUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma log_le_of_memR_upper_le_logUpperBound_eq
  {I : RatInterval}
  {x u v : ℝ}
-- given
  (hx : I.MemR x)
  (hx_pos : 0 < x)
  (hIu : (I.upper : ℝ) ≤ u)
  (huv : LogUpperBound u v) :
-- imply
  Real.log x ≤ v := by
-- proof
  apply StatMech.Exact3D.RatInterval.log_le_of_memR_upper_le_logUpperBound hx hx_pos hIu huv

/--
[log_le_of_positive_memR_upper_le_logUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma log_le_of_positive_memR_upper_le_logUpperBound_eq
  {I : RatInterval}
  {x u v : ℝ}
-- given
  (hI : I.Positive)
  (hx : I.MemR x)
  (hIu : (I.upper : ℝ) ≤ u)
  (huv : LogUpperBound u v) :
-- imply
  Real.log x ≤ v := by
-- proof
  apply StatMech.Exact3D.RatInterval.log_le_of_positive_memR_upper_le_logUpperBound hI hx hIu huv

/--
[log_le_of_memR_upper_le_ratLogUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma log_le_of_memR_upper_le_ratLogUpperBound_eq
  {I : RatInterval}
  {x : ℝ}
  {u v : ℚ}
-- given
  (hx : I.MemR x)
  (hx_pos : 0 < x)
  (hIu : I.upper ≤ u)
  (huv : RatLogUpperBound u v) :
-- imply
  Real.log x ≤ (v : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.log_le_of_memR_upper_le_ratLogUpperBound hx hx_pos hIu huv

/--
[log_le_of_positive_memR_upper_le_ratLogUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma log_le_of_positive_memR_upper_le_ratLogUpperBound_eq
  {I : RatInterval}
  {x : ℝ}
  {u v : ℚ}
-- given
  (hI : I.Positive)
  (hx : I.MemR x)
  (hIu : I.upper ≤ u)
  (huv : RatLogUpperBound u v) :
-- imply
  Real.log x ≤ (v : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.log_le_of_positive_memR_upper_le_ratLogUpperBound hI hx hIu huv

/--
[le_log_of_logLowerBound_le_lower_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma le_log_of_logLowerBound_le_lower_memR_eq
  {I : RatInterval}
  {x l a : ℝ}
-- given
  (hla : LogLowerBound l a)
  (haI : a ≤ (I.lower : ℝ))
  (hx : I.MemR x) :
-- imply
  l ≤ Real.log x := by
-- proof
  apply StatMech.Exact3D.RatInterval.le_log_of_logLowerBound_le_lower_memR hla haI hx

/--
[le_log_of_ratLogLowerBound_le_lower_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma le_log_of_ratLogLowerBound_le_lower_memR_eq
  {I : RatInterval}
  {x : ℝ}
  {l a : ℚ}
-- given
  (hla : RatLogLowerBound l a)
  (haI : a ≤ I.lower)
  (hx : I.MemR x) :
-- imply
  (l : ℝ) ≤ Real.log x := by
-- proof
  apply StatMech.Exact3D.RatInterval.le_log_of_ratLogLowerBound_le_lower_memR hla haI hx

/--
[exp_le_of_memR_upper_le_expUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma exp_le_of_memR_upper_le_expUpperBound_eq
  {I : RatInterval}
  {x u r : ℝ}
-- given
  (hx : I.MemR x)
  (hIu : (I.upper : ℝ) ≤ u)
  (hur : ExpUpperBound u r) :
-- imply
  Real.exp x ≤ r := by
-- proof
  apply StatMech.Exact3D.RatInterval.exp_le_of_memR_upper_le_expUpperBound hx hIu hur

/--
[exp_le_of_memR_upper_le_ratExpUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma exp_le_of_memR_upper_le_ratExpUpperBound_eq
  {I : RatInterval}
  {x : ℝ}
  {u r : ℚ}
-- given
  (hx : I.MemR x)
  (hIu : I.upper ≤ u)
  (hur : RatExpUpperBound u r) :
-- imply
  Real.exp x ≤ (r : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.exp_le_of_memR_upper_le_ratExpUpperBound hx hIu hur

/--
[exp_lower_le_exp_of_lower_le_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma exp_lower_le_exp_of_lower_le_memR_eq
  {I : RatInterval}
  {x l : ℝ}
-- given
  (hlI : l ≤ (I.lower : ℝ))
  (hx : I.MemR x) :
-- imply
  Real.exp l ≤ Real.exp x := by
-- proof
  apply StatMech.Exact3D.RatInterval.exp_lower_le_exp_of_lower_le_memR hlI hx

/--
[rat_exp_lower_le_exp_of_lower_le_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean)
-/
@[path]
private lemma rat_exp_lower_le_exp_of_lower_le_memR_eq
  {I : RatInterval}
  {x : ℝ}
  {l : ℚ}
-- given
  (hlI : l ≤ I.lower)
  (hx : I.MemR x) :
-- imply
  Real.exp (l : ℝ) ≤ Real.exp x := by
-- proof
  apply StatMech.Exact3D.RatInterval.rat_exp_lower_le_exp_of_lower_le_memR hlI hx


-- created on 2026-10-23
