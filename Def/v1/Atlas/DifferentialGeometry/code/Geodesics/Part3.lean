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
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Intrinsic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part4
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
public import Abbrev.v1.Atlas.DifferentialGeometry.code.GaussMap
public import Structure.v1.Atlas.DifferentialGeometry.code.Geodesics.Part2

@[expose] public section

open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

namespace Geodesics

def pathLength {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖

def reversePath {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) :
    SmoothPathIn M q p where
  toFun := fun t => γ.toFun (1 - t)
  smooth := fun m => (γ.smooth m).comp (by fun_prop)
  source := by simp [γ.target]
  target := by simp [γ.source]
  maps_to := fun t => γ.maps_to _

def geodesicDist (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  sInf {l | ∃ γ : SmoothPathIn M p q, pathLength γ = l}

def IsSmoothOnHypersurface {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Set E) (f : ↥M → ℝ) : Prop :=
  ∀ (y : E) (hy : y ∈ M), ∃ (V : Set E) (hV : IsOpen V) (hyV : y ∈ V)
    (f_ext : E → ℝ), ContDiffOn ℝ ⊤ f_ext V ∧
    ∀ z (hzM : z ∈ M) (_ : z ∈ V), f_ext z = f ⟨z, hzM⟩

end Geodesics
end
