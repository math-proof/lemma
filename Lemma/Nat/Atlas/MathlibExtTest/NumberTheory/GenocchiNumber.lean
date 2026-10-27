import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.GenocchiNumber


namespace MetaMathlibExtTest

/--
[invExpAddOne_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GenocchiNumber.lean)
-/
@[path]
private lemma invExpAddOne_coeff_zero :
  PowerSeries.coeff 0 ((PowerSeries.exp ℚ + 1)⁻¹) = 1 / 2 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv]
  norm_num

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[invExpAddOne_coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GenocchiNumber.lean)
-/
@[path]
private lemma invExpAddOne_coeff_one :
  PowerSeries.coeff 1 ((PowerSeries.exp ℚ + 1)⁻¹) = -1 / 4 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, invExpAddOne_coeff_zero]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[invExpAddOne_coeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GenocchiNumber.lean)
-/
@[path]
private lemma invExpAddOne_coeff_two :
  PowerSeries.coeff 2 ((PowerSeries.exp ℚ + 1)⁻¹) = 0 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, invExpAddOne_coeff_zero, invExpAddOne_coeff_one]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[invExpAddOne_coeff_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GenocchiNumber.lean)
-/
@[path]
private lemma invExpAddOne_coeff_three :
  PowerSeries.coeff 3 ((PowerSeries.exp ℚ + 1)⁻¹) = 1 / 48 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, invExpAddOne_coeff_zero, invExpAddOne_coeff_one,
    invExpAddOne_coeff_two, Nat.factorial]

end MetaMathlibExtTest


-- created on 2026-10-23
