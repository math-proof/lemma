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
import Theorem.Analysis.SpecialFunctions.ExpSubOneMittagLeffler
/-!
# Mittag-Leffler expansion of the Bose-Einstein kernel
-/


namespace MetaMathlibExt

open scoped BigOperators

open Complex

noncomputable section

def expSubOnePole (m : ℕ) : ℝ :=
  2 * Real.pi * (m + 1)

def expSubOneKernelTerm (v : ℝ) (m : ℕ) : ℝ :=
  2 * v / (v ^ 2 + expSubOnePole m ^ 2)

def expSubOneKernelCoeff (n m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ n / expSubOnePole m ^ (2 * n + 2)

def expSubOneRemainderTerm (N : ℕ) (v : ℝ) (m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ N * v ^ (2 * N + 1) /
    (expSubOnePole m ^ (2 * N) * (v ^ 2 + expSubOnePole m ^ 2))

def expSubOneRemainderDerivTerm (N : ℕ) (v : ℝ) (m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ N / expSubOnePole m ^ (2 * N) *
    (((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / (v ^ 2 + expSubOnePole m ^ 2) -
      2 * v ^ (2 * N + 2) / (v ^ 2 + expSubOnePole m ^ 2) ^ 2)

def expSubOneRemainder (N : ℕ) (v : ℝ) : ℝ :=
  ∑' m : ℕ, expSubOneRemainderTerm N v m

def expSubOneBound (N : ℕ) : ℝ :=
  2 * (2 * N + 3 : ℕ) * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹

end
end MetaMathlibExt
