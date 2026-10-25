/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14LagrangeSeries.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.Algebra.Polynomial
import Lemma.Complex.ExpOfContinuousAddMul
import Def.NumberTheory.Ramanujan.Part1Ch3Entry13CorollarySchroder
import Lemma.Nat.Ramanujan.Part1Ch3Entry13CorollarySchroder
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 14

This file proves Ramanujan's Lagrange series, including convergence on the boundary circle.
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry14LagrangeSeries

open scoped Interval Topology

/-- The polynomial coefficient occurring in Ramanujan's Lagrange series. -/
def lagrangeSeriesCoefficient (p q n : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else
    n * ∏ j ∈ Finset.range (k - 1), (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)

noncomputable def ch3E14Coeff (p q n : ℝ) (k : ℕ) : ℝ :=
  lagrangeSeriesCoefficient p q n k / (Nat.factorial k : ℝ)

noncomputable def ch3E14Polynomial (p q : ℝ) (k : ℕ) : Polynomial ℝ :=
  if k = 0 then 1 else
    Polynomial.C ((Nat.factorial k : ℝ)⁻¹) * Polynomial.X *
      ∏ j ∈ Finset.range (k - 1),
        (Polynomial.X + Polynomial.C ((k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q))

noncomputable def ch3E14Term (p q : ℝ) (a : ℂ) (n : ℝ) (k : ℕ) : ℂ :=
  (ch3E14Coeff p q n k : ℂ) * a ^ k

noncomputable def ch3E14F (p q : ℝ) (a : ℂ) (n : ℝ) : ℂ :=
  ∑' k : ℕ, ch3E14Term p q a n k

end Entry14LagrangeSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
