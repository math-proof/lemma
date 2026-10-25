/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification15_19_40_45.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Juntas
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceDerivative
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
import Def.v1.Atlas.BooleanFunctions.code.Juntas
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierSampling
import Def.v1.Atlas.BooleanFunctions.code.InfluenceDerivative
import Def.v1.Atlas.BooleanFunctions.code.Talagrand
import Def.v1.Atlas.BooleanFunctions.code.MajorityStablest
open Finset BigOperators


namespace BooleanFourier

example {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n))
    (hf : ∀ x, |f x| ≤ 1) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ ⌈2 * Real.log (2 / δ) / ε ^ 2⌉₊ ∧
      ((Finset.univ.filter (fun samples : Fin m → (Fin n → Bool) =>
        |((1 : ℝ) / m) * ∑ i : Fin m, f (samples i) * chi S (samples i)
          - fourierCoeff f S| ≥ ε)).card : ℝ) / ((2 : ℝ) ^ n) ^ m
        ≤ δ :=
  claim_1_2_fourier_sampling f S hf ε hε δ hδ hδ2


example {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    fourierCoeff f S = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * chi S x :=
  fourierCoeff_eq_expectation f S


example {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n))
    (hf : ∀ x, |f x| ≤ 1) (x : Fin n → Bool) :
    |f x * chi S x| ≤ 1 :=
  sample_bounded f S hf x


example {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (i : Fin (n + 1)) :
    influence f i =
      (∑ y : Fin n → Bool,
        (boolDiscreteDerivative (fun x => boolToSign (f x)) i y) ^ 2) /
        (2 ^ n : ℝ) :=
  influence_eq_l2_norm_sq_discreteDerivative f i


example {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    fourierCoeff f S ^ 2 ≤ (1 / (S.card : ℝ)) * ∑ i ∈ S, fourierInfluence f i :=
  fourierCoeff_sq_le_avg_fourierInfluence f S hS


example (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      HasBoundedRange01 f →
      boolExpectation f = 1 / 2 →
      (∀ i : Fin n, influenceReal f i ≤ δ) →
      noiseStability ρ f ≤ halfspaceNoiseStability01 ρ (1 / 2) + ε :=
  majority_is_stablest_theorem01 ρ hρ₀ hρ₁ ε hε

end BooleanFourier
