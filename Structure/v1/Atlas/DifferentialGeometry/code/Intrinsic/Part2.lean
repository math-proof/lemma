/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part3


public noncomputable section

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
