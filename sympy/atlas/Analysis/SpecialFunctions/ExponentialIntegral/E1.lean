/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean -/

import sympy.atlas.Analysis.SpecialFunctions.EntireExponentialIntegral
import Lemma.Complex.EntireExponentialIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

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

/-- Totalized principal-`E1` kernel `Ein z - Log z - γ`.

This is a junk-value extension: at `z = 0` it evaluates to `-γ` via
`Complex.log 0 = 0`, not to the classical principal `E1`, which is singular
there. Use `principalExponentialIntegralE1` with a `z ≠ 0` proof for the
domain-safe API. -/
def principalExponentialIntegralE1Raw (z : ℂ) : ℂ :=
  ein z - Complex.log z - (Real.eulerMascheroniConstant : ℂ)

/-- Principal `E1` on `ℂ \ {0}`, represented by the standard DLMF 6.2.4 connection
`E1 z = Ein z - Log z - gamma`.  Uses of the sourced asymptotic remainder
exclude `z = 0` and the branch cut. -/
def principalExponentialIntegralE1 (z : ℂ) (_hz : z ≠ 0) : ℂ :=
  principalExponentialIntegralE1Raw z

/-- Totalized `n`-th asymptotic-expansion term.

At `z = 0` the divisions by zero evaluate to junk (`x / 0 = 0`), hence the
term is `0`, with no classical meaning. Use `e1AsymptoticTerm` with a `z ≠ 0`
proof for the domain-safe API. -/
def e1AsymptoticTermRaw (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z) / z *
    ((-1 : ℂ) ^ n * (n.factorial : ℂ) / z ^ n)

/-- The `n`-th full term in the finite asymptotic expansion of `E1`. -/
def e1AsymptoticTerm (n : ℕ) (z : ℂ) (_hz : z ≠ 0) : ℂ :=
  e1AsymptoticTermRaw n z

/-- Totalized sum of the first `n` raw asymptotic terms.

Junk-value extension: at `z = 0` this is `0`. Use `e1AsymptoticPartial` with
a `z ≠ 0` proof for the domain-safe API. -/
def e1AsymptoticPartialRaw (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, e1AsymptoticTermRaw j z

/-- The first `n` terms in the finite asymptotic expansion of `E1`. -/
def e1AsymptoticPartial (n : ℕ) (z : ℂ) (hz : z ≠ 0) : ℂ :=
  ∑ j ∈ Finset.range n, e1AsymptoticTerm j z hz

/-- Totalized exact remainder of the raw partial sums.

Junk-value extension: at `z = 0` this is `-γ`. Use `e1AsymptoticRemainder`
with a `z ≠ 0` proof for the domain-safe API. -/
def e1AsymptoticRemainderRaw (n : ℕ) (z : ℂ) : ℂ :=
  principalExponentialIntegralE1Raw z - e1AsymptoticPartialRaw n z

/-- The exact remainder after the first `n` asymptotic terms. -/
def e1AsymptoticRemainder (n : ℕ) (z : ℂ) (hz : z ≠ 0) : ℂ :=
  principalExponentialIntegralE1 z hz - e1AsymptoticPartial n z hz

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
