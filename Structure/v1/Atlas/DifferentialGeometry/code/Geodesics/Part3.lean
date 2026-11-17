/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part6
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Manifolds
public import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Intrinsic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part4
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
public import Abbrev.v1.Atlas.DifferentialGeometry.code.GaussMap
public import Def.v1.Atlas.DifferentialGeometry.code.Geodesics.Part3
open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


public noncomputable section

namespace Geodesics

structure ConnectedHypersurface (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin (n + 1)))
  isHypersurface : IsHypersurface carrier
  connected : ∀ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
    (∀ y ∈ carrier, ContDiffAt ℝ ⊤ φ y) →
    (∀ y ∈ carrier, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      IsLocalDefiningFunction ψ carrier y →
      ∀ v ∈ tangentSpace ψ y, fderiv ℝ φ y v = 0) →
    (∀ y₁ ∈ carrier, ∀ y₂ ∈ carrier, φ y₁ = φ y₂)

structure ConnectedHypersurfaceWithPaths (n : ℕ) extends ConnectedHypersurface n where
  pathConnected : ∀ p q : EuclideanSpace ℝ (Fin (n + 1)),
    p ∈ carrier → q ∈ carrier → Nonempty (SmoothPathIn carrier p q)

end Geodesics
end
