import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1
open scoped BigOperators
open Complex


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

/--
[principalExponentialIntegralE1Raw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma principalExponentialIntegralE1Raw_zero_eq
  :
-- imply
  principalExponentialIntegralE1Raw 0 = -(Real.eulerMascheroniConstant : ℂ) := by
-- proof
  apply Complex.principalExponentialIntegralE1Raw_zero

/--
[e1AsymptoticTermRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma e1AsymptoticTermRaw_zero_eq
  {n : ℕ} :
-- imply
  e1AsymptoticTermRaw n 0 = 0 := by
-- proof
  apply Complex.e1AsymptoticTermRaw_zero n

/--
[e1AsymptoticPartialRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma e1AsymptoticPartialRaw_zero_eq
  {n : ℕ} :
-- imply
  e1AsymptoticPartialRaw n 0 = 0 := by
-- proof
  apply Complex.e1AsymptoticPartialRaw_zero n

/--
[e1AsymptoticRemainderRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean)
-/
@[path]
private lemma e1AsymptoticRemainderRaw_zero_eq
  {n : ℕ} :
-- imply
  e1AsymptoticRemainderRaw n 0 = -(Real.eulerMascheroniConstant : ℂ) := by
-- proof
  apply Complex.e1AsymptoticRemainderRaw_zero n


-- created on 2026-10-20
