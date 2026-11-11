/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/LocalDeMoivreLaplace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Floor
open Asymptotics Filter Real Topology Nat


noncomputable section

namespace ProbabilityTheory

/-- The point mass `P(S_n = k) = C(n,k) / 2ⁿ` for a `Binomial(n, 1/2)` random variable `S_n`. -/
def binomProbHalf (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) / (2 : ℝ) ^ n

/-- The Gaussian (local CLT) approximation to `binomProbHalf n k`,
`√(2/(π n)) · exp(-(k - n/2)² / (n/2))`. -/
def gaussianApproxHalf (n : ℕ) (k : ℕ) : ℝ :=
  Real.sqrt (2 / (Real.pi * (n : ℝ))) *
    Real.exp (-(((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2)))

/-- The integer index `k = ⌊n/2 + x·√n/2⌋` corresponding to the parameter `x` in the local
DeMoivre–Laplace statement: it picks the lattice point near `n/2 + x √n / 2`, so that
`(2k - n)/√n ≈ x`. -/
def localDMLIndex (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) / 2 + x * Real.sqrt (n : ℝ) / 2⌋₊

end ProbabilityTheory
end
