/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification69_74.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.UncoveredBatch3
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.UncoveredBatch3
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Poincare
open Finset BigOperators


namespace BooleanFourier

example {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : IsMonotone f) (i : Fin n) :
    0 ≤ fourierCoeff (fun x => boolToReal (f x)) {i} :=
  monotone_fourierCoeff_singleton_nonneg f hf i


example {n : ℕ} (f : BoolFn n) :
    variance f ≤ totalInfluenceReal f :=
  poincare_inequality f


example {n : ℕ} (hn : 0 < n) (δ : ℝ) :
    noiseSensitivity δ (fun x : Fin n → Bool => x ⟨0, hn⟩) = δ :=
  noiseSensitivity_dictator hn δ


example {n : ℕ} (f : (Fin n → Bool) → Bool) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    noiseSensitivity δ f ≤ δ * totalInfluence f :=
  noiseSensitivity_le_totalInfluence_mul_delta f δ hδ0 hδ1

end BooleanFourier
