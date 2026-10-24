/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# Mittag-Leffler expansion of the Bose-Einstein kernel
-/

namespace MetaMathlibExt

open scoped BigOperators
open Complex

noncomputable section

private def expSubOnePole (m : ℕ) : ℝ :=
  2 * Real.pi * (m + 1)

private def expSubOneKernelTerm (v : ℝ) (m : ℕ) : ℝ :=
  2 * v / (v ^ 2 + expSubOnePole m ^ 2)

private def expSubOneKernelCoeff (n m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ n / expSubOnePole m ^ (2 * n + 2)

private def expSubOneRemainderTerm (N : ℕ) (v : ℝ) (m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ N * v ^ (2 * N + 1) /
    (expSubOnePole m ^ (2 * N) * (v ^ 2 + expSubOnePole m ^ 2))

private def expSubOneRemainderDerivTerm (N : ℕ) (v : ℝ) (m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ N / expSubOnePole m ^ (2 * N) *
    (((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / (v ^ 2 + expSubOnePole m ^ 2) -
      2 * v ^ (2 * N + 2) / (v ^ 2 + expSubOnePole m ^ 2) ^ 2)

private def expSubOneRemainder (N : ℕ) (v : ℝ) : ℝ :=
  ∑' m : ℕ, expSubOneRemainderTerm N v m

private def expSubOneBound (N : ℕ) : ℝ :=
  2 * (2 * N + 3 : ℕ) * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹

/-- The analytic remainder after truncating the Laurent expansion of
`1 / (Real.exp v - 1)` after `N` odd-power terms. -/
def oneDivExpSubOneLaurentRemainder (N : ℕ) (v : ℝ) : ℝ :=
  if v = 0 then 0 else
    1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
      ∑ n ∈ Finset.range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          v ^ (2 * n + 1)
end
