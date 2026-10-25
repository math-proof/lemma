/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Structure.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part3
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

open scoped SchwartzMap

namespace SchwartzRepresentation

variable {n : ℕ}

/-- Order `|α| = α₁ + ⋯ + α_n` of a multi-index `α : Fin n → ℕ`. -/
def multiIndexOrder (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- The finite set of all multi-indices `α : Fin n → ℕ` with `|α| ≤ m`. -/
def multiIndicesBall (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (m + 1))).filter
    (fun α => multiIndexOrder α ≤ m)

/-- The monomial `x^α = ∏ x_i^{α_i}` viewed as a complex-valued function on
`ℝ^n`. -/
def monomial (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∏ i : Fin n, (↑(x i) : ℂ) ^ (α i)

/-- Iterate the line derivative `∂_{x_j}` exactly `k` times on a Schwartz
function. -/
def iterSchwartzDerivCoord (j : Fin n) (k : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)))^[k] φ

/-- The multi-index partial derivative `∂^β` on Schwartz functions, defined by
iteratively applying coordinate derivatives in each direction `j` exactly
`β j` times. -/
def iterSchwartzDeriv (β : Fin n → ℕ) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j ψ => iterSchwartzDerivCoord j (β j) ψ) φ

end SchwartzRepresentation
end
