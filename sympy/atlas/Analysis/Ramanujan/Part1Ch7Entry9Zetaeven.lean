/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry9Zetaeven.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Phi
import sympy.atlas.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Lemma.Complex.Part1Ch7DirichletBeta
import Lemma.Real.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
import Lemma.Real.Ramanujan.Part1Ch7Entry8Bernoullibound
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry8Bernoullibound
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry9Zetaeven

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry10Zetaviabernoulli (chapter7Admissible chapter7PowerDifferenceTerm)
open Entry8Bernoullibound (chapter7BernoulliPolynomial chapter7IntegerPhi)

noncomputable section

private def chap7W (x : ℂ) (j : ℕ) : ℂ := x / ((j : ℂ) + 1)

private def chap7R (K : ℕ) (r w : ℂ) : ℂ :=
  (1 + w) ^ r - ∑ k ∈ Finset.range (K + 1), Ring.choose r k * w ^ k

private def chap7g (K J : ℕ) (x : ℂ) (n : ℕ) (r : ℂ) : ℂ :=
  -((((n + J : ℕ) : ℂ) + 1) ^ r * chap7R K r (chap7W x (n + J)))

private def chap7U (m : ℕ) : Set ℂ := {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ)}

private def chap7S (m N : ℕ) : Set ℂ :=
  {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ) ∧ ‖r‖ < (N : ℝ)}

private def chap7G (K J : ℕ) (x : ℂ) (r : ℂ) : ℂ :=
  ∑' n : ℕ, chap7g K J x n r

private def chap7E : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

private def chap7P (k : ℕ) (r : ℂ) : ℂ :=
  ∏ i ∈ Finset.range (k - 1), (r - (i : ℂ))

private def chap7H (J : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range J, ((((j : ℕ) : ℂ) + 1) ^ (-s))

private def chap7T (x : ℂ) (j : ℕ) (r : ℂ) : ℂ :=
  ((((j : ℕ) : ℂ) + 1) ^ r - ((((j : ℕ) : ℂ) + 1 + x) ^ r))

private def chap7PhiCont (K J : ℕ) (x : ℂ) (r : ℂ) : ℂ :=
  (∑ j ∈ Finset.range J, chap7T x j r) +
    (∑' n : ℕ, chap7g K J x n r) +
    ∑ k ∈ Finset.Icc 1 K,
      x ^ k * (chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
        Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r))
end
end Entry9Zetaeven
end MathlibExt.Analysis.Ramanujan.Part1Ch7
