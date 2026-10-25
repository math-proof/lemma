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
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
open Real Set Topology


noncomputable section

namespace CM8

section HarmonicProofHelpers

open Finset

/-- The Green function $G(x, y) = \Phi_3(x - y) - \phi(x, y)$ assembled from a
fundamental solution and its corrector. -/
def GreenFunction.G {Ω : Set (Fin 3 → ℝ)} (gf : GreenFunction Ω)
    (x y : Fin 3 → ℝ) : ℝ :=
  Phi3 (x - y) - gf.corrector x y

/-- Abstract placeholder for the outward normal derivative
$\nabla_{\hat{N}(\sigma)} f$ of a function $f$ at a boundary point $\sigma$ of
$\Omega$. -/
opaque normalDerivGF (Ω : Set (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ)
    (σ : Fin 3 → ℝ) : ℝ

/-- Abstract placeholder for the boundary surface integral
$\int_{\partial \Omega} f(\sigma) \, d\sigma$. -/
opaque surfaceIntegralGF (Ω : Set (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ) : ℝ

/-- Abstract placeholder for the integral of $f$ over the sphere of radius
$\varepsilon$ centred at $x$: $\int_{\partial B_\varepsilon(x)} f \, d\sigma$. -/
opaque sphereIntegralGF (x : Fin 3 → ℝ) (ε : ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ


end HarmonicProofHelpers
end CM8
end
