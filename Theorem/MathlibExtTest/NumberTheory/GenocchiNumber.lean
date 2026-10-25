/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GenocchiNumber.lean -/


import Def.NumberTheory.GenocchiNumber
import Lemma.Nat.GenocchiNumber
import Mathlib.Tactic.NormNum


namespace MetaMathlibExtTest

example : MetaMathlibExt.genocchiPowerSeries
    = 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹ :=
  rfl

example (n : ℕ) : MetaMathlibExt.genocchiNumber n
    = (n.factorial : ℚ) * (PowerSeries.coeff n) MetaMathlibExt.genocchiPowerSeries :=
  MetaMathlibExt.genocchiNumber_eq n

example : MetaMathlibExt.genocchiNumber 0 = 0 := by
  simp [MetaMathlibExt.genocchiNumber, MetaMathlibExt.genocchiPowerSeries]

example : MetaMathlibExt.genocchiNumber 1 = 1 := by
  change (1 : ℚ) * PowerSeries.coeff 1
    (PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹) = 1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    invExpAddOne_coeff_zero]
  norm_num

example : MetaMathlibExt.genocchiNumber 2 = -1 := by
  change (2 : ℚ) * PowerSeries.coeff 2
    (PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹) = -1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    invExpAddOne_coeff_one]
  norm_num

example : MetaMathlibExt.genocchiNumber 4 = 1 := by
  change (24 : ℚ) * PowerSeries.coeff 4
    (PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹) = 1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    invExpAddOne_coeff_three]
  norm_num

end MetaMathlibExtTest
