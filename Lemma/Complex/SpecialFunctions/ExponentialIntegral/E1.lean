import Mathlib
import sympy.Basic
import Theorem.Analysis.SpecialFunctions.ExponentialIntegral.E1
open scoped BigOperators
open Complex


namespace Complex

/--
[principalExponentialIntegralE1Raw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
lemma principalExponentialIntegralE1Raw_zero
  :
-- imply
  principalExponentialIntegralE1Raw 0 = -(Real.eulerMascheroniConstant : ℂ) := by
-- proof
  have hein : ein (0 : ℂ) = 0 := by simp [ein, einTerm]
  simp [principalExponentialIntegralE1Raw, hein, Complex.log_zero]

end Complex

namespace Complex

/--
[e1AsymptoticTermRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
lemma e1AsymptoticTermRaw_zero
  {n : ℕ} :
-- imply
  e1AsymptoticTermRaw n 0 = 0 := by
-- proof
  simp [e1AsymptoticTermRaw]

end Complex

namespace Complex

/--
[e1AsymptoticPartialRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
lemma e1AsymptoticPartialRaw_zero
  {n : ℕ} :
-- imply
  e1AsymptoticPartialRaw n 0 = 0 := by
-- proof
  simp [e1AsymptoticPartialRaw, e1AsymptoticTermRaw_zero]

end Complex

namespace Complex

/--
[e1AsymptoticRemainderRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
lemma e1AsymptoticRemainderRaw_zero
  {n : ℕ} :
-- imply
  e1AsymptoticRemainderRaw n 0 = -(Real.eulerMascheroniConstant : ℂ) := by
-- proof
  simp [e1AsymptoticRemainderRaw, principalExponentialIntegralE1Raw_zero,
    e1AsymptoticPartialRaw_zero]
end


/--
[principalExponentialIntegralE1_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma principalExponentialIntegralE1_eq_raw_eq
  {z : ℂ}
-- given
  (hz : z ≠ 0) :
-- imply
  principalExponentialIntegralE1 z hz = principalExponentialIntegralE1Raw z := by
-- proof
  apply Complex.principalExponentialIntegralE1_eq_raw z hz

/--
[e1AsymptoticTerm_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma e1AsymptoticTerm_eq_raw_eq
  {n : ℕ}
  {z : ℂ}
-- given
  (hz : z ≠ 0) :
-- imply
  e1AsymptoticTerm n z hz = e1AsymptoticTermRaw n z := by
-- proof
  apply Complex.e1AsymptoticTerm_eq_raw n z hz

/--
[e1AsymptoticPartial_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma e1AsymptoticPartial_eq_raw_eq
  {n : ℕ}
  {z : ℂ}
-- given
  (hz : z ≠ 0) :
-- imply
  e1AsymptoticPartial n z hz = e1AsymptoticPartialRaw n z := by
-- proof
  apply Complex.e1AsymptoticPartial_eq_raw n z hz

/--
[e1AsymptoticRemainder_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma e1AsymptoticRemainder_eq_raw_eq
  {n : ℕ}
  {z : ℂ}
-- given
  (hz : z ≠ 0) :
-- imply
  e1AsymptoticRemainder n z hz = e1AsymptoticRemainderRaw n z := by
-- proof
  apply Complex.e1AsymptoticRemainder_eq_raw n z hz


-- created on 2026-10-20
-- updated on 2026-10-23
