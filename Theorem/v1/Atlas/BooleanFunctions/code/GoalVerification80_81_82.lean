/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification80_81_82.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Borel
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Borel
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.NoiseStabilityBounds
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.NoiseStabilityMono
set_option maxHeartbeats 800000

open Finset BigOperators Real MeasureTheory ProbabilityTheory


example {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hf_balanced : ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    GaussianStability.gaussianNoiseStability ρ hρ₀ hρ₁ f ≤ 2 / π * arcsin ρ :=
  GaussianStability.borel_isoperimetric_core f hf_range hf_balanced ρ hρ₀ hρ₁


example {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hf_balanced : ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    GaussianStability.gaussianNoiseStability ρ hρ₀ hρ₁ f ≤ 1 - (2 / π) * arccos ρ :=
  GaussianStability.borel_isoperimetric_theorem f hf_range hf_balanced ρ hρ₀ hρ₁


example {n : ℕ} (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → ℝ) :
    BooleanFourier.fourierCoeff f ∅ ^ 2 ≤ BooleanFourier.noiseStability ρ f ∧
    BooleanFourier.noiseStability ρ f ≤
      ∑ S : Finset (Fin n), BooleanFourier.fourierCoeff f S ^ 2 :=
  BooleanFourier.noiseStability_bounds ρ hρ₀ hρ₁ f


example {n : ℕ} (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → Bool) :
    BooleanFourier.fourierCoeff (fun x => BooleanFourier.boolToReal (f x)) ∅ ^ 2
      ≤ BooleanFourier.noiseStability ρ (fun x => BooleanFourier.boolToReal (f x)) ∧
    BooleanFourier.noiseStability ρ (fun x => BooleanFourier.boolToReal (f x)) ≤ 1 :=
  BooleanFourier.noiseStability_bounds_boolean ρ hρ₀ hρ₁ f


example {n : ℕ} (ρ σ : ℝ) (hρ₀ : 0 ≤ ρ) (hρσ : ρ ≤ σ)
    (f : (Fin n → Bool) → ℝ) :
    BooleanFourier.noiseStability ρ f ≤ BooleanFourier.noiseStability σ f :=
  BooleanFourier.noiseStability_mono ρ σ hρ₀ hρσ f


example {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    BooleanFourier.noiseStability 0 f = BooleanFourier.fourierCoeff f ∅ ^ 2 :=
  BooleanFourier.noiseStability_at_zero f


example {n : ℕ} (f : (Fin n → Bool) → Bool) :
    BooleanFourier.noiseStability 1 (fun x => BooleanFourier.boolToReal (f x)) = 1 :=
  BooleanFourier.noiseStability_at_one_of_boolean f


example {n : ℕ} (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → Bool) :
    BooleanFourier.fourierCoeff (fun x => BooleanFourier.boolToReal (f x)) ∅ ^ 2
      ≤ BooleanFourier.noiseStability ρ (fun x => BooleanFourier.boolToReal (f x)) ∧
    BooleanFourier.noiseStability ρ (fun x => BooleanFourier.boolToReal (f x)) ≤ 1 :=
  BooleanFourier.noiseStability_bounds_of_boolean ρ hρ₀ hρ₁ f

