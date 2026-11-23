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
public import Structure.v1.Atlas.DifferentialGeometry.code.Geodesics.Part4

@[expose] public section

open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

section GeodesicDistance

variable {n : ℕ}

section HopfRinow

variable {n : ℕ}

def IsRiemannianGeodesicallyComplete (M : ConnectedHypersurface n) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ M.carrier)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M.carrier y)
    (Y : EuclideanSpace ℝ (Fin (n + 1))) (hY : Y ∈ Hypersurface.tangentSpace ψ y),
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      IsGeodesic M.carrier M.isHypersurface γ ∧ γ 0 = y ∧ deriv γ 0 = Y

def IsMetricallyComplete (M : ConnectedHypersurface n) : Prop :=
  ∀ (x : ℕ → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ i, x i ∈ M.carrier) →
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ k ≥ N, geodesicDist M.carrier (x m) (x k) < ε) →
    ∃ p ∈ M.carrier, ∀ ε > 0, ∃ N, ∀ m ≥ N, geodesicDist M.carrier (x m) p < ε

def IsMinimizingGeodesic (M : ConnectedHypersurface n)
    (p q : EuclideanSpace ℝ (Fin (n + 1)))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)))
    (a b : ℝ) : Prop :=
  IsGeodesic M.carrier M.isHypersurface γ ∧
  γ a = p ∧ γ b = q ∧
    ∀ σ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      ContDiff ℝ ⊤ σ → (∀ t, σ t ∈ M.carrier) → σ a = p → σ b = q →
      energy γ a b ≤ energy σ a b

end HopfRinow

def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ (p q : X), ∃ (γ : ℝ → X),
    IsMetricGeodesic γ 0 (dist p q) ∧ γ 0 = p ∧ γ (dist p q) = q

def IsCATZeroSpace (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧
  ∀ (p₁ p₂ p₃ : X)
    (γ₁₂ γ₁₃ γ₂₃ : ℝ → X),

    IsMetricGeodesic γ₁₂ 0 (dist p₁ p₂) →
    γ₁₂ 0 = p₁ → γ₁₂ (dist p₁ p₂) = p₂ →
    IsMetricGeodesic γ₁₃ 0 (dist p₁ p₃) →
    γ₁₃ 0 = p₁ → γ₁₃ (dist p₁ p₃) = p₃ →
    IsMetricGeodesic γ₂₃ 0 (dist p₂ p₃) →
    γ₂₃ 0 = p₂ → γ₂₃ (dist p₂ p₃) = p₃ →

    ∀ (q₁ q₂ q₃ : EuclideanSpace ℝ (Fin 2)),
    dist q₁ q₂ = dist p₁ p₂ →
    dist q₁ q₃ = dist p₁ p₃ →
    dist q₂ q₃ = dist p₂ p₃ →

    ∀ (t : ℝ) (s : ℝ),
    t ∈ Set.Icc 0 (dist p₁ p₂) →
    s ∈ Set.Icc 0 (dist p₁ p₃) →

    dist (γ₁₂ t) (γ₁₃ s) ≤
      dist ((1 - t / dist p₁ p₂) • q₁ + (t / dist p₁ p₂) • q₂)
           ((1 - s / dist p₁ p₃) • q₁ + (s / dist p₁ p₃) • q₃)

end GeodesicDistance
end
