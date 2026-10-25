/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FriedgutKalai.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Monotone
import Def.v1.Atlas.BooleanFunctions.code.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Finset Real


namespace BooleanFourier

noncomputable def pBiasedProb {n : ℕ} (f : (Fin n → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ x : Fin n → Bool,
    (if f x = true then 1 else 0) *
    (∏ i : Fin n, if x i = true then p else (1 - p))

noncomputable def thresholdValue {n : ℕ} (f : (Fin n → Bool) → Bool) (ε : ℝ) : ℝ :=
  Classical.epsilon (fun p => 0 ≤ p ∧ p ≤ 1 ∧ pBiasedProb f p = ε)


end BooleanFourier
