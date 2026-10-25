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
open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

namespace Geodesics

def IsGeodesic {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t, γ t ∈ M) ∧
  (∀ t, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)

def energy {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖ ^ 2

end Geodesics
end
