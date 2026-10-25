/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry19Gaussdigamma.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Batteries.Util.ProofWanted
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Def.Analysis.Calculus.EulerMaclaurinFormula
import Lemma.Real.Calculus.EulerMaclaurinFormula
import Lemma.Real.Ramanujan.Part1Ch7Entry1Powersum
import Def.Analysis.Ramanujan.Part1Ch7Entry1Powersum
/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 19

This file proves Ramanujan's asymptotic expansion for the binomial combination of log-power sums
in Entry 19 and identifies their constant terms with derivatives of the Riemann zeta function.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry19Gaussdigamma

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum

noncomputable section

def chapter8Entry19Approx (n x : ℕ) : ℝ :=
  (n.factorial : ℝ) * x -
    (((bernoulli (n + 1) : ℚ) : ℝ) /
      ((n + 1 : ℕ) * (x : ℝ) ^ n)) -
    ((n : ℝ) * ((bernoulli (n + 2) : ℚ) : ℝ) /
      (2 * (n + 2 : ℕ) * (x : ℝ) ^ (n + 1))) -
    ((n : ℝ) * ((n : ℝ) + 5 / 3) *
      ((bernoulli (n + 3) : ℚ) : ℝ) /
      (8 * (n + 3 : ℕ) * (x : ℝ) ^ (n + 2)))

def chapter8LogPowerSum (m x : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 x, Real.log (k : ℝ) ^ m

def chapter8LogPowerConstant (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m *
    iteratedDeriv m (fun s : ℝ => (riemannZeta (s : ℂ)).re) 0

def chapter8Psi (m x : ℕ) : ℝ :=
  chapter8LogPowerSum m x - chapter8LogPowerConstant m

def chapter8Entry19Combination (n x : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (-1 : ℝ) ^ (n + k) * (n.choose k : ℝ) *
      Real.log (x : ℝ) ^ k * chapter8Psi (n - k) x

def chapter8LogPowerConstantApprox (m x : ℕ) : ℝ :=
  chapter8LogPowerSum m x -
    (∫ t in (1 : ℝ)..(x : ℝ), Real.log t ^ m) -
    (1 / 2 : ℝ) * Real.log (x : ℝ) ^ m +
    (-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ)

noncomputable def ch8e19Kernel (p : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun p (Int.fract x)

noncomputable def ch8e19MellinBase (N : ℕ) (x : ℝ) : ℂ :=
  if 1 ≤ x then (ch8e19Kernel (2 * N + 1) x : ℂ) else 0

noncomputable def ch8e19MellinIntegral (N : ℕ) (r : ℂ) : ℂ :=
  mellin (ch8e19MellinBase N) (r - (2 * N + 1 : ℕ) + 1)

noncomputable def ch8e19Tail (N : ℕ) (r : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Set.Ioi (n : ℝ),
    (x : ℂ) ^ (r - (2 * N + 1 : ℕ)) * (ch8e19Kernel (2 * N + 1) x : ℂ)

noncomputable def ch8e19RemainderFactor (N : ℕ) (r : ℂ) : ℂ :=
  chapter7FallingGammaRatio r (2 * N + 1) / ((2 * N + 1).factorial : ℂ)

noncomputable def ch8e19Constant (N : ℕ) (r : ℂ) : ℂ :=
  1 / 2 - 1 / (r + 1) - ∑ j ∈ Finset.range N, chapter7Entry1Term r 1 j +
    ch8e19RemainderFactor N r * ch8e19MellinIntegral N r

noncomputable def ch8e19LogPrimitive : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | m + 1 => fun x => x * Real.log x ^ (m + 1) - (m + 1) * ch8e19LogPrimitive m x

noncomputable def ch8e19Error (N x : ℕ) (r : ℂ) : ℂ :=
  chapter7PowerSum r x - riemannZeta (-r) -
    chapter7NatCpow x (r + 1) / (r + 1) - chapter7NatCpow x r / 2 -
      ∑ j ∈ Finset.range N, chapter7Entry1Term r x j

noncomputable def ch8e19EntryCoeff (j : ℕ) (r : ℂ) : ℂ :=
  let k := j + 1
  (((bernoulli (2 * k) : ℚ) : ℂ) / ((2 * k).factorial : ℂ)) *
    chapter7FallingGammaRatio r (2 * k - 1)

noncomputable def ch8e19ScaledError (N x : ℕ) (r : ℂ) : ℂ :=
  chapter7NatCpow x (-r) * ch8e19Error N x r

noncomputable def ch8e19ScaledTerm (x j : ℕ) (r : ℂ) : ℂ :=
  chapter7NatCpow x (-r) * chapter7Entry1Term r x j

noncomputable def ch8e19ScaledSum (x : ℕ) (r : ℂ) : ℂ :=
  chapter7NatCpow x (-r) * (chapter7PowerSum r x - riemannZeta (-r))

noncomputable def ch8e19CorrectionTerm (n j x : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (iteratedDeriv n (ch8e19ScaledTerm x j) 0).re

noncomputable def ch8e19FirstCorrection (n x : ℕ) : ℝ :=
  -(((bernoulli (n + 1) : ℚ) : ℝ) /
    ((n + 1 : ℕ) * (x : ℝ) ^ n))

noncomputable def ch8e19SecondCorrection (n x : ℕ) : ℝ :=
  -((n : ℝ) * ((bernoulli (n + 2) : ℚ) : ℝ) /
    (2 * (n + 2 : ℕ) * (x : ℝ) ^ (n + 1)))

noncomputable def ch8e19ThirdCorrection (n x : ℕ) : ℝ :=
  -((n : ℝ) * ((n : ℝ) + 5 / 3) *
    ((bernoulli (n + 3) : ℚ) : ℝ) /
      (8 * (n + 3 : ℕ) * (x : ℝ) ^ (n + 2)))

end
end Entry19Gaussdigamma
end MathlibExt.Analysis.Ramanujan.Part1Ch8
