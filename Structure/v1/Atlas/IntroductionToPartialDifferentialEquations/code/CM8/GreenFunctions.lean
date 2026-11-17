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
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
open Real Set Topology


public noncomputable section

namespace CM8

section HarmonicProofHelpers

open Finset

/-- **Definition 2.0.2 (Green function for a domain).** Data of a Green
function for a domain $\Omega \subset \mathbb{R}^3$: a `corrector`
$\phi(x, y)$ which matches the fundamental solution on the boundary, i.e.
$\phi(x, \sigma) = \Phi_3(x - \sigma)$ for $x \in \Omega$ and $\sigma \in
\partial \Omega$. -/
structure GreenFunction (Ω : Set (Fin 3 → ℝ)) where
  corrector : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω,
    corrector x σ = Phi3 (x - σ)

end HarmonicProofHelpers
end CM8
end
