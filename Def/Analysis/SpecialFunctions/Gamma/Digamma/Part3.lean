/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Theorem.Analysis.SpecialFunctions.Gamma.Digamma.Part2

@[expose] public section

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

def digammaFun (s : ℂ) : ℂ :=
  Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)

end Complex
end
