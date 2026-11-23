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
public import Structure.v1.Atlas.DifferentialGeometry.code.Geodesics.Part3

@[expose] public section

open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

section GeodesicDistance

variable {n : ℕ}

def lengthAB {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖

section EnergyLengthEquivalence

variable {n : ℕ}

def pathEnergy {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖ ^ 2

def IsConstantSpeed {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∃ c : ℝ, ∀ t, ‖deriv γ.toFun t‖ = c

def IsAbsoluteLengthMinimizer {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∀ σ : SmoothPathIn M p q, pathLength γ ≤ pathLength σ

def IsAbsoluteEnergyMinimizer {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∀ σ : SmoothPathIn M p q, pathEnergy γ ≤ pathEnergy σ

end EnergyLengthEquivalence

def IsMetricGeodesic {X : Type*} [MetricSpace X] (γ : ℝ → X) (a b : ℝ) : Prop :=
  Continuous γ ∧ ∀ s t, s ∈ Set.Icc a b → t ∈ Set.Icc a b → dist (γ s) (γ t) = |s - t|

def IsGlobalMetricGeodesic {X : Type*} [MetricSpace X] (γ : ℝ → X) : Prop :=
  ∀ s t : ℝ, dist (γ s) (γ t) = |s - t|

end GeodesicDistance
end
