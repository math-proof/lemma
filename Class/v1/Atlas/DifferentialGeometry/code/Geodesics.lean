module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part6
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part4
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
public import Abbrev.v1.Atlas.DifferentialGeometry.code.GaussMap
public import Def.v1.Atlas.DifferentialGeometry.code.Geodesics.Part5
public section
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
