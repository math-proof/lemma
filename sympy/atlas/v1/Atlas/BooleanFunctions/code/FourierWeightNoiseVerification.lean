/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierWeightNoiseVerification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.UncoveredTargets
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.UncoveredTargets

open Finset BigOperators

namespace BooleanFourier

example {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 1 ∨ f x = -1)
    (K : ℝ) (hK : (∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2) ≤ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
        (fun S => (S.card : ℝ) > 2 * K / ε),
        (fourierCoeff f S) ^ 2 ≤ ε :=
  low_degree_concentration f hf K hK ε hε

example {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) :
    fourierWeightUpToLevel k f =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k),
        (fourierCoeff f S) ^ 2 := rfl

example {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), ρ ^ S.card * (fourierCoeff f S) ^ 2 =
      ∑ k ∈ Finset.range (n + 1), ρ ^ k * fourierWeightAtLevel k f :=
  noiseStability_via_weight ρ f

example {n : ℕ} (ρ : ℝ) (hρ : |ρ| ≤ 1) (k : ℕ) (f : (Fin n → Bool) → ℝ) :
    fourierWeightUpToLevel k (noiseOperator ρ f) ≤ fourierWeightUpToLevel k f :=
  level_k_inequality ρ hρ k f

example {n : ℕ} (ρ : ℝ) (f g : (Fin n → Bool) → ℝ) :
    innerProduct (noiseOperator ρ f) g = innerProduct f (noiseOperator ρ g) :=
  noiseOp_self_adjoint ρ f g

end BooleanFourier
