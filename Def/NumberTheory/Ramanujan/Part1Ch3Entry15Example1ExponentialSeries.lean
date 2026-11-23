/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15Example1ExponentialSeries.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Polynomial
public import Def.NumberTheory.Ramanujan.Part1Ch3Entry14Cor1Catalanpowerseries
public import Theorem.Nat.Ramanujan.Part1Ch3Entry14Cor1Catalanpowerseries

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

The main theorem proves Entry 15, Example 1, evaluating Ramanujan's exponential series as
`2 ^ m` for `0 < n ≤ 2`.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15Example1ExponentialSeries

noncomputable def abelB (m n : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    (m * ∏ i ∈ Finset.range k, (m + (k + 1 : ℕ) * n - 1 - i))
      / (Nat.factorial (k + 1) : ℝ)

noncomputable def gchoose (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    (∏ i ∈ Finset.range (k + 1), (r - i)) / (Nat.factorial (k + 1) : ℝ)

noncomputable def BpolyM (N k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.X * (∏ i ∈ Finset.range j,
      (Polynomial.X + Polynomial.C (((j + 1 : ℕ) : ℝ) * (N : ℝ) - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

noncomputable def GpolyM (N T : ℕ) (R : ℝ) (k : ℕ) :
    Polynomial ℝ :=
  (∏ i ∈ Finset.range (T - k),
    (Polynomial.C (R - (N : ℝ) * (k : ℝ) - (i : ℝ)) - Polynomial.X))
    * Polynomial.C (((Nat.factorial (T - k) : ℝ))⁻¹)

noncomputable def BpolyN (M : ℝ) (k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.C M
      * (∏ i ∈ Finset.range j,
        (Polynomial.C (((j + 1 : ℕ)) : ℝ) * Polynomial.X
          + Polynomial.C (M - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

noncomputable def GpolyN (M : ℝ) (T : ℕ) (R : ℝ) (k : ℕ) :
    Polynomial ℝ :=
  (∏ i ∈ Finset.range (T - k),
    (Polynomial.C (R - M - (i : ℝ)) - Polynomial.X * Polynomial.C (k : ℝ)))
    * Polynomial.C (((Nat.factorial (T - k) : ℝ))⁻¹)

noncomputable def expSeries_Bpoly (n : ℝ) (k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.X * (∏ i ∈ Finset.range j,
      (Polynomial.X + Polynomial.C (((j + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

noncomputable def expSeries_F (m n x : ℝ) : ℝ :=
  ∑' k : ℕ, abelB m n k * x ^ k

noncomputable def expSeries_phi (n y : ℝ) : ℝ :=
  (y - 1) / y ^ n

end Entry15Example1ExponentialSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
