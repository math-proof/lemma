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
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
open Real Set Topology


noncomputable section

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
