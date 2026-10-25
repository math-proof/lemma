/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean -/

import Def.Analysis.SpecialFunctions.EntireExponentialIntegral
import Lemma.Complex.EntireExponentialIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Def.Analysis.SpecialFunctions.ExponentialIntegral.E1
/-!
# Principal exponential-integral definitions

This module fixes the principal `E1` and asymptotic-remainder normalizations
used by the local DLMF proof. It introduces no assumptions.

The classical principal `E1` has a logarithmic singularity at `z = 0`, so the
standard-named definitions below take an explicit `z ≠ 0` proof argument. The
`Raw`-suffixed helpers are totalized extensions that reuse Lean's junk values
(`Complex.log 0 = 0`, `x / 0 = 0`); they exist so internal differentiability
arguments and the zero-value regressions can be stated, and must not be used
as the classical `E1` at the singular point.
-/


namespace Complex

noncomputable section

open scoped BigOperators

@[simp] theorem principalExponentialIntegralE1_eq_raw (z : ℂ) (hz : z ≠ 0) :
    principalExponentialIntegralE1 z hz = principalExponentialIntegralE1Raw z :=
  rfl

@[simp] theorem e1AsymptoticTerm_eq_raw (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    e1AsymptoticTerm n z hz = e1AsymptoticTermRaw n z :=
  rfl

@[simp] theorem e1AsymptoticPartial_eq_raw (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    e1AsymptoticPartial n z hz = e1AsymptoticPartialRaw n z := by
  simp only [e1AsymptoticPartial, e1AsymptoticPartialRaw, e1AsymptoticTerm_eq_raw]

@[simp] theorem e1AsymptoticRemainder_eq_raw (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    e1AsymptoticRemainder n z hz = e1AsymptoticRemainderRaw n z := by
  simp only [e1AsymptoticRemainder, e1AsymptoticRemainderRaw,
    principalExponentialIntegralE1_eq_raw, e1AsymptoticPartial_eq_raw]

end
end Complex
