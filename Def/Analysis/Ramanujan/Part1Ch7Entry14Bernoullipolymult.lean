/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.NumberTheory.Bernoulli
import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Lemma.Complex.Part1Ch7DirichletBeta
import Lemma.Real.Part1Ch7Entry13Bernoullipolyadd
import Lemma.Real.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
import Lemma.Real.ExpSubOneMittagLeffler
import Def.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
import Def.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Def.Analysis.SpecialFunctions.ExpSubOneMittagLeffler
import Abbrev.Analysis.Ramanujan.Part1Ch7Entry14Bernoullipolymult
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 14

This file proves the convergence and finite-order asymptotic expansion of Ramanujan's
Bernoulli-polynomial series in terms of the Stieltjes constants.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry14Bernoullipolymult

open scoped Nat Real BigOperators Interval

open Asymptotics Filter Finset Topology MeasureTheory

noncomputable section

def entry14Bound (N : ℕ) : ℝ :=
  2 * (2 * N + 3 : ℕ) *
    ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹

def entry14Phi (N : ℕ) (x t : ℝ) : ℝ :=
  entry14Remainder N (x * Real.log t) / t

def entry14PhiDeriv (N : ℕ) (x t : ℝ) : ℝ :=
  (x * deriv (entry14Remainder N) (x * Real.log t) -
    entry14Remainder N (x * Real.log t)) / t ^ 2

def entry14Majorant (N j : ℕ) : ℝ :=
  Real.log ((j : ℝ) + 2) ^ (2 * N) / ((j : ℝ) + 1) ^ 2 +
    Real.log ((j : ℝ) + 2) ^ (2 * N + 1) / ((j : ℝ) + 1) ^ 2

def entry14Delta (N : ℕ) (x : ℝ) (j : ℕ) : ℝ :=
  entry14Phi N x ((j : ℝ) + 2) -
    ∫ t in ((j : ℝ) + 1)..((j : ℝ) + 2), entry14Phi N x t

def entry14KernelPrimitive (v : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-v)) - Real.log v

def entry14PrimitiveTerm (n : ℕ) (v : ℝ) : ℝ :=
  (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) /
    (2 * n + 2 : ℕ) * v ^ (2 * n + 2)

def entry14PolyPrimitive (N : ℕ) (v : ℝ) : ℝ :=
  v / 2 - ∑ n ∈ range N, entry14PrimitiveTerm n v

def entry14Primitive (N : ℕ) (v : ℝ) : ℝ :=
  entry14KernelPrimitive v + entry14PolyPrimitive N v

def entry14ScaledPrimitive (N : ℕ) (x t : ℝ) : ℝ :=
  entry14Primitive N (x * Real.log t) / x

def chapter7Entry14A0Approx (m : ℕ) : ℝ :=
  (∑ k ∈ Icc 2 m, 1 / ((k : ℝ) * Real.log k)) -
    Real.log (Real.log m)

def chapter7StieltjesA (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * c k / (k.factorial : ℝ)

def chapter7Entry14Coeff (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  -((bernoulli (2 * k) : ℚ) : ℝ) * chapter7StieltjesA c (2 * k - 1) /
    (2 * k)

def chapter7Entry14Approx (a0 : ℝ) (c : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (a0 - Real.log x) / x +
    (1 - Real.eulerMascheroniConstant) / 2 +
    ∑ j ∈ range N, chapter7Entry14Coeff c (j + 1) * x ^ (2 * j + 1)

def chapter7Entry14Term (x : ℝ) (j : ℕ) : ℝ :=
  let k : ℝ := j + 2
  1 / (k * (Real.rpow k x - 1))

def chapter7Entry14Sum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter7Entry14Term x j

def chapter7StieltjesApprox (k m : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / j) -
    Real.log (m : ℝ) ^ (k + 1) / (k + 1)

def entry14FiniteMain (N : ℕ) (x : ℝ) (m : ℕ) : ℝ :=
  (chapter7Entry14A0Approx (m + 1) - Real.log x) / x +
    (1 - ((((harmonic (m + 1) : ℚ)) : ℝ) - Real.log ((m : ℝ) + 1))) / 2 +
    ∑ n ∈ range N,
      ((bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
        x ^ (2 * n + 1)) * chapter7StieltjesApprox (2 * n + 1) (m + 1)

def entry14Boundary (x : ℝ) (m : ℕ) : ℝ :=
  Real.log (1 - Real.exp (-x * Real.log ((m : ℝ) + 1))) / x

end
end Entry14Bernoullipolymult
end MathlibExt.Analysis.Ramanujan.Part1Ch7
