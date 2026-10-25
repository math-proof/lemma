/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry1Powersum.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.Calculus.EulerMaclaurinFormula
import Lemma.Real.Calculus.EulerMaclaurinFormula
/-!
# Ramanujan's asymptotic expansion for power sums

This file proves the Euler--Maclaurin asymptotic expansion of finite sums of arbitrary complex
powers, including the identification of the constant term with the Riemann zeta function.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry1Powersum

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7NatCpow (n : ℕ) (r : ℂ) : ℂ :=
  Complex.cpow (n : ℂ) r

def chapter7FallingGammaRatio (r : ℂ) (q : ℕ) : ℂ :=
  ∏ j ∈ range q, (r - (j : ℂ))

def chapter7Entry1Term (r : ℂ) (n j : ℕ) : ℂ :=
  let k := j + 1
  (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
    chapter7FallingGammaRatio r (2 * k - 1) *
      chapter7NatCpow n (r - (2 * k : ℕ) + 1)

def chapter7Entry1Approx (r : ℂ) (N n : ℕ) : ℂ :=
  riemannZeta (-r) + chapter7NatCpow n (r + 1) / (r + 1) +
    chapter7NatCpow n r / 2 + ∑ j ∈ range N, chapter7Entry1Term r n j

def chapter7PowerSum (r : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 n, chapter7NatCpow k r

noncomputable def ch7Entry1Kernel (p : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun p (Int.fract x)

noncomputable def ch7Entry1MellinBase (N : ℕ) (x : ℝ) : ℂ :=
  if 1 ≤ x then (ch7Entry1Kernel (2 * N + 1) x : ℂ) else 0

noncomputable def ch7Entry1MellinIntegral (N : ℕ) (r : ℂ) : ℂ :=
  mellin (ch7Entry1MellinBase N) (r - (2 * N + 1 : ℕ) + 1)

noncomputable def ch7Entry1Tail (N : ℕ) (r : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Set.Ioi (n : ℝ),
    (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch7Entry1Kernel (2 * N + 1) x : ℂ)

noncomputable def ch7Entry1RemainderFactor (N : ℕ) (r : ℂ) : ℂ :=
  chapter7FallingGammaRatio r (2 * N + 1) / ((2 * N + 1).factorial : ℂ)

noncomputable def ch7Entry1Constant (N : ℕ) (r : ℂ) : ℂ :=
  1 / 2 - 1 / (r + 1) - ∑ j ∈ Finset.range N, chapter7Entry1Term r 1 j +
    ch7Entry1RemainderFactor N r * ch7Entry1MellinIntegral N r

end
end Entry1Powersum
end MathlibExt.Analysis.Ramanujan.Part1Ch7
