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
import Def.v1.Atlas.DifferentialGeometry.code.Geodesics.Part5
open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

section GeodesicDistance

variable {n : ℕ}

class IsBusemannSpace (X : Type*) [MetricSpace X] : Prop where
  isGeodesicSpace : IsGeodesicSpace X
  busemann_inequality : ∀ (l : ℝ) (hl : 0 < l)
    (γ₁ γ₂ : ℝ → X)
    (hγ₁ : IsMetricGeodesic γ₁ 0 l) (hγ₂ : IsMetricGeodesic γ₂ 0 l)
    (h_start : γ₁ 0 = γ₂ 0)
    (t : ℝ) (ht : t ∈ Set.Icc 0 l),
    dist (γ₁ t) (γ₂ t) ≤ (t / l) * dist (γ₁ l) (γ₂ l)

end GeodesicDistance
end
