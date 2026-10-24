/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15Example1ExponentialSeries.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry14Cor1Catalanpowerseries
import Lemma.Nat.Ramanujan.Part1Ch3Entry14Cor1Catalanpowerseries
section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

The main theorem proves Entry 15, Example 1, evaluating Ramanujan's exponential series as
`2 ^ m` for `0 < n ≤ 2`.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15Example1ExponentialSeries

private noncomputable def abelB (m n : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    (m * ∏ i ∈ Finset.range k, (m + (k + 1 : ℕ) * n - 1 - i))
      / (Nat.factorial (k + 1) : ℝ)

private noncomputable def gchoose (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    (∏ i ∈ Finset.range (k + 1), (r - i)) / (Nat.factorial (k + 1) : ℝ)

private noncomputable def BpolyM (N k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.X * (∏ i ∈ Finset.range j,
      (Polynomial.X + Polynomial.C (((j + 1 : ℕ) : ℝ) * (N : ℝ) - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

private noncomputable def GpolyM (N T : ℕ) (R : ℝ) (k : ℕ) :
    Polynomial ℝ :=
  (∏ i ∈ Finset.range (T - k),
    (Polynomial.C (R - (N : ℝ) * (k : ℝ) - (i : ℝ)) - Polynomial.X))
    * Polynomial.C (((Nat.factorial (T - k) : ℝ))⁻¹)

private noncomputable def BpolyN (M : ℝ) (k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.C M
      * (∏ i ∈ Finset.range j,
        (Polynomial.C (((j + 1 : ℕ)) : ℝ) * Polynomial.X
          + Polynomial.C (M - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

private noncomputable def GpolyN (M : ℝ) (T : ℕ) (R : ℝ) (k : ℕ) :
    Polynomial ℝ :=
  (∏ i ∈ Finset.range (T - k),
    (Polynomial.C (R - M - (i : ℝ)) - Polynomial.X * Polynomial.C (k : ℝ)))
    * Polynomial.C (((Nat.factorial (T - k) : ℝ))⁻¹)

private noncomputable def expSeries_Bpoly (n : ℝ) (k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.X * (∏ i ∈ Finset.range j,
      (Polynomial.X + Polynomial.C (((j + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

private noncomputable def expSeries_F (m n x : ℝ) : ℝ :=
  ∑' k : ℕ, abelB m n k * x ^ k

private noncomputable def expSeries_phi (n y : ℝ) : ℝ :=
  (y - 1) / y ^ n
end Entry15Example1ExponentialSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
