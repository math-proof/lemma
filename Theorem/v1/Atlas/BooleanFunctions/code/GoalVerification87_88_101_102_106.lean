/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification87_88_101_102_106.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.UncoveredBatch3
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.UncoveredBatch3
import Def.v1.Atlas.BooleanFunctions.code.MajorityStablest
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Corollary12Lec11
open Finset BigOperators


example (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      BooleanFourier.HasBoundedRange f →
      BooleanFourier.maxInfluence f ≤ δ →
      BooleanFourier.noiseStability ρ f ≤
        BooleanFourier.halfspaceNoiseStability ρ (BooleanFourier.boolExpectation f) + ε :=
  BooleanFourier.majority_is_stablest_general ρ hρ₀ hρ₁ ε hε


example {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), (S.card : ℝ) * BooleanFourier.fourierCoeff f S ^ 2 =
    ∑ i : Fin n, BooleanFourier.fourierInfluence f i :=
  BooleanFourier.spectral_sample_expected_cardinality f


example :
    UGCHardness.UGC → ∀ ε : ℝ, ε > 0 →
      MaxCut.IsNPHardGapMaxCut (1 - ε) (MaxCut.goemansWilliamsonConstant + ε) :=
  UGCHardness.goemansWilliamson_optimal_assuming_ugc


example (hUGC : UGCHardness.UGC) :
    ∀ ε : ℝ, ε > 0 →
      MaxCut.IsNPHardGapMaxCut (1 - ε) (MaxCut.goemansWilliamsonConstant + ε) :=
  UGCHardness.corollary_1_2 hUGC


example {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (ρ₁ ρ₂ : ℝ)
    (hρ₁ : 0 ≤ ρ₁) (hρ₁' : ρ₁ ≤ 1) (hρ₂ : 0 ≤ ρ₂) (hρ₂' : ρ₂ ≤ 1) (hle : ρ₁ ≤ ρ₂) :
    GaussianStability.gaussianNoiseStability ρ₁ hρ₁ hρ₁' f ≤
    GaussianStability.gaussianNoiseStability ρ₂ hρ₂ hρ₂' f :=
  GaussianStability.gaussianNoiseStability_mono f ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hle

