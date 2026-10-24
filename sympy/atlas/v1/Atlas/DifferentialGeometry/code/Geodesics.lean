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
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Manifolds
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Manifolds
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Intrinsic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Intrinsic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.GaussMap

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

structure SmoothVariation {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) where
  Γ : ℝ → ℝ → EuclideanSpace ℝ (Fin (n + 1))
  smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Γ p.1 p.2)
  base : ∀ t, Γ 0 t = γ t
  left_fixed : ∀ s, Γ s a = γ a
  right_fixed : ∀ s, Γ s b = γ b
  maps_to : ∀ s t, Γ s t ∈ M

def firstVariationEnergy {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) : ℝ :=
  deriv (fun s => energy (V.Γ s) a b) 0

def variationField {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  deriv (fun s => V.Γ s t) 0

def IsEnergyMinimizer {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : Prop :=
  ∀ V : SmoothVariation M γ a b, ∀ s : ℝ, energy γ a b ≤ energy (V.Γ s) a b

def IsGeodesicOn {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (I : Set ℝ) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t ∈ I, γ t ∈ M) ∧
  (∀ t ∈ I, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)

def SatisfiesGeodesicEquation {n : ℕ} (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ) : Prop :=
  ContDiff ℝ ⊤ c ∧
  (∀ t, c t ∈ patch.domain) ∧
  (∀ t, ∀ k : Fin n,
    (deriv (deriv c) t) k +
      ∑ i : Fin n, ∑ j : Fin n,
        ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
          (deriv c t i) * (deriv c t j) = 0)

structure SmoothPathIn (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) where
  toFun : ℝ → EuclideanSpace ℝ (Fin (n + 1))
  smooth : ∀ (m : ℕ∞), ContDiff ℝ m toFun
  source : toFun 0 = p
  target : toFun 1 = q
  maps_to : ∀ t, toFun t ∈ M

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

end GeodesicDistance

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

class IsBusemannSpace (X : Type*) [MetricSpace X] : Prop where
  isGeodesicSpace : IsGeodesicSpace X
  busemann_inequality : ∀ (l : ℝ) (hl : 0 < l)
    (γ₁ γ₂ : ℝ → X)
    (hγ₁ : IsMetricGeodesic γ₁ 0 l) (hγ₂ : IsMetricGeodesic γ₂ 0 l)
    (h_start : γ₁ 0 = γ₂ 0)
    (t : ℝ) (ht : t ∈ Set.Icc 0 l),
    dist (γ₁ t) (γ₂ t) ≤ (t / l) * dist (γ₁ l) (γ₂ l)
