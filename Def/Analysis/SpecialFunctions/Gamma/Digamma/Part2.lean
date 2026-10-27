/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Theorem.Analysis.SpecialFunctions.Gamma.Digamma
open scoped Real
open Filter Finset Topology

/-!
# Series and analyticity facts for Gamma and digamma

For `x > 0`, the digamma series `∑ (1/(j+1) - 1/(x+j+1))` sums to `ψ(x+1) + γ`, where
`ψ = (log ∘ Gamma)'`, and its termwise derivative gives the trigamma series `∑ 1/(y+j+1)²`.
The file also proves that `Complex.Gamma` and `Complex.digamma` are analytic away from the
nonpositive integers, that the complex derivative of `Gamma` restricts to the real one on
`(0, ∞)`, and that `∑ 1/(z+k+1)²` converges absolutely for every complex `z` away from the
negative integers, and that for `1 < s.re` the complex digamma function satisfies
the expansion `ψ(s) + γ = ∑ j, (1/(j+1) - 1/(j+s))` (as a `HasSum` statement).
-/


noncomputable section

namespace Complex

/-- The half-plane `Re s > 1` where the complex digamma series converges. -/
def seriesDomain : Set ℂ := {s : ℂ | 1 < s.re}

/-- Complex digamma series term: `1/(j+1) - 1/(j+s)`. -/
def digammaSeriesTerm (j : ℕ) (s : ℂ) : ℂ :=
  1 / ((j : ℂ) + 1) - 1 / ((j : ℂ) + s)

/-- Complex digamma series function. -/
def digammaSeriesFun (s : ℂ) : ℂ := ∑' j : ℕ, digammaSeriesTerm j s

end Complex
end
