/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part6
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Manifolds
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Intrinsic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part4
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Abbrev.v1.Atlas.DifferentialGeometry.code.GaussMap
import Def.v1.Atlas.DifferentialGeometry.code.Geodesics.Part4
open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

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
