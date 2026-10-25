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
import Structure.v1.Atlas.DifferentialGeometry.code.Geodesics.Part3
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
