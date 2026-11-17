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
public import Def.v1.Atlas.DifferentialGeometry.code.Geodesics.Part4
open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


public noncomputable section

section GeodesicDistance

variable {n : ℕ}

section Hadamard

variable {n : ℕ}

structure CompactPositiveGaussCurvature (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin (n + 1)))
  isHypersurface : IsHypersurface carrier
  isCompact : IsCompact carrier
  isConnected : IsConnected carrier
  gaussCurvaturePos : ∀ (patch : HypersurfacePatch n) (x : Fin n → ℝ),
    x ∈ patch.domain →
    (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ carrier →
    0 < gaussCurvature patch x

end Hadamard
end GeodesicDistance
end
