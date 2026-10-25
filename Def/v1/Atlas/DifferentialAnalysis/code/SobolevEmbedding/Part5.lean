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
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part2
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

open scoped SchwartzMap

namespace SchwartzRepresentation

variable {n : ℕ}

section SchwartzLpEmbedding

open MeasureTheory

/-- Map a Schwartz function `φ` to the `L^2` equivalence class of `∂^α φ`. -/
noncomputable def schwartzToLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (schwartzDerivMemLp n α φ).toLp _

/-- Pairing `⟨f, φ⟩ = ∫ f(x) · φ(x) dx` of a `C_0` function `f` against a
Schwartz function `φ`, used to express tempered distributions of the form
arising in the Schwartz representation theorem. -/
def c0SchwartzPairing
    (f : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : ℂ :=
  ∫ x, f x * φ x


set_option maxHeartbeats 1600000 in

/-- Joint `L^2 → C_0` decomposition: a finite sum `∑_α ∫ g_α · ∂^α φ` over
`|α| ≤ m` of `L^2`-functions can be rewritten as `∑_γ c0SchwartzPairing (v γ) (∂^γ φ)`
with each `v γ` a `C_0` function. -/
def multiIndicesBelow (n : ℕ) (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (γ i + 1))

end SchwartzLpEmbedding
end SchwartzRepresentation
end
