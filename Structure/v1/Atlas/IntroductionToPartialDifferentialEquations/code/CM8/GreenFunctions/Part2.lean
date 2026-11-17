/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
open Real Set Topology


public noncomputable section

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
