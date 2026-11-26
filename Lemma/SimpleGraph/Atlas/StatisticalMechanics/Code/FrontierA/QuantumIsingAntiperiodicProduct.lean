import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct.Part2
open StatMech StatMech.FrontierA


/--
[prod_one_sub_quantumIsingAntiperiodicRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean)
-/
@[path]
private lemma prod_one_sub_quantumIsingAntiperiodicRoot_eq
  {n : Nat}
  {z : Complex}
-- given
  (hn : n ≠ 0) :
-- imply
  (∏ j < n, (1 - z * quantumIsingAntiperiodicRoot n j)) = 1 + z ^ n := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  apply StatMech.FrontierA.prod_one_sub_quantumIsingAntiperiodicRoot n hn z

/--
[prod_sub_cos_quantumIsingAntiperiodicAngle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean)
-/
@[path]
private lemma prod_sub_cos_quantumIsingAntiperiodicAngle_eq
  {n : Nat}
  {r : Real}
-- given
  (hn : n ≠ 0)
  (hr : 0 < r) :
-- imply
  (∏ j < n, ((r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j))) = (r / 2) ^ n * (1 + r⁻¹ ^ n) ^ 2 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  apply StatMech.FrontierA.prod_sub_cos_quantumIsingAntiperiodicAngle n hn r hr

/--
[sum_log_sub_cos_quantumIsingAntiperiodicAngle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean)
-/
@[path]
private lemma sum_log_sub_cos_quantumIsingAntiperiodicAngle_eq
  {n : Nat}
  {r : Real}
-- given
  (hn : n ≠ 0)
  (hr : 1 < r) :
-- imply
  (∑ j < n, Real.log ((r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j))) = -(n : Real) * Real.log 2 + (n : Real) * Real.log r + 2 * Real.log (1 + r⁻¹ ^ n) := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  apply StatMech.FrontierA.sum_log_sub_cos_quantumIsingAntiperiodicAngle n hn r hr


-- created on 2026-10-23
