/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification_0_8_10_11_12_13.lean -/

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


example {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x = fourierCoeff f ∅ := by
  simp only [fourierCoeff, chi_empty, mul_one]


example {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    f x = ∑ S : Finset (Fin n), fourierCoeff f S * chi S x :=
  fourier_expansion f x


example {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 = 1 :=
  parseval_pm_one f hf


example {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (· ≠ ∅),
      (fourierCoeff f S) ^ 2 = 1 - (fourierCoeff f ∅) ^ 2 :=
  variance_pm_one f hf


example {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) :
    fourierWeightAtLevel k f =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k),
        (fourierCoeff f S) ^ 2 :=
  rfl


example {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2 =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) * fourierWeightAtLevel k f :=
  totalInfluence_eq_weighted_degree f

end BooleanFourier
