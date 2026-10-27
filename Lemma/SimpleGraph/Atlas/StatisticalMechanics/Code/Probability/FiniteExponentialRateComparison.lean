import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.FiniteExponentialRateComparison
open Filter Topology StatMech StatMech.Probability


/--
[pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FiniteExponentialRateComparison.lean)
-/
@[path]
private lemma pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow_eq
  {a b tail corr : Real}
  {k height : Nat}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (htail : 0 < tail)
  (hcorr : 0 < corr)
  (hheight : 0 < height)
  (h : a * tail <= b * corr ^ k) :
-- imply
  (k : Real) * (-Real.log corr / (height : Real)) <= -Real.log tail / (height : Real) + (Real.log b - Real.log a) / (height : Real) := by
-- proof
  apply StatMech.Probability.pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow ha hb htail hcorr hheight h

/--
[pow_negLogRate_le_negLogRate_of_mul_le_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FiniteExponentialRateComparison.lean)
-/
@[path]
private lemma pow_negLogRate_le_negLogRate_of_mul_le_mul_pow_eq
  {tail corr : Nat -> Real}
  {height : Nat -> Nat}
  {a b tailRate corrRate : Real}
  {k : Nat}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (htail : forall n, 0 < tail n)
  (hcorr : forall n, 0 < corr n)
  (hheightPos : forall n, 0 < height n)
  (hheight : Tendsto height atTop atTop)
  (hbound : forall n, a * tail n <= b * corr n ^ k)
  (htailRate : Tendsto (fun n => -Real.log (tail n) / (height n : Real)) atTop (nhds tailRate))
  (hcorrRate : Tendsto (fun n => -Real.log (corr n) / (height n : Real)) atTop (nhds corrRate)) :
-- imply
  (k : Real) * corrRate <= tailRate := by
-- proof
  apply StatMech.Probability.pow_negLogRate_le_negLogRate_of_mul_le_mul_pow ha hb htail hcorr hheightPos hheight hbound htailRate hcorrRate


-- created on 2026-10-23
