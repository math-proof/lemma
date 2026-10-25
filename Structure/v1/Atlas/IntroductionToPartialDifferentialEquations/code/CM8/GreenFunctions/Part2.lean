/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
open Real Set Topology


noncomputable section

namespace CM8

section HarmonicProofHelpers

open Finset

/-- Green's identity on the punctured domain $\Omega \setminus B_\varepsilon(x)$:
the volume integral of $\Phi_3(x - y) \Delta u(y)$ equals a difference of
boundary surface integrals minus a sphere integral around the singularity. -/
structure IsGreenDecomposition {n : ℕ} (Ω : Set (Fin n → ℝ))
    (Φ : (Fin n → ℝ) → ℝ)
    (G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (φ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop where
  decomposition : ∀ x y : Fin n → ℝ, G x y = Φ (x - y) - φ x y
  corrector_harmonic : ∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (φ x) y = 0
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, φ x σ = Φ (x - σ)

end HarmonicProofHelpers
end CM8
end
