/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part3


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace GaussBonnetTorus

open MeasureTheory MovingFrame

structure RiemannianMetric (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  domain_nonempty : domain.Nonempty
  G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  smooth : ContDiffOn ℝ ⊤ G domain
  symmetric : ∀ x ∈ domain, (G x)ᵀ = G x
  posDef : ∀ x ∈ domain, (G x).PosDef

end AbstractRiemannianMetric

namespace AbstractGaussBonnet

open MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure RiemannianMetric2D where
  G : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  smooth : ContDiff ℝ ⊤ G
  symmetric : ∀ x, (G x)ᵀ = G x
  posDef : ∀ x, (G x).PosDef

end AbstractGaussBonnet
end ChristoffelSymbols
end
