module
public import Def.v1.Atlas.BooleanFunctions.code.Monotone
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Monotone
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.NoiseSensitivity
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.UniqueGames
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Theorems
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Lemma26Lec10
public import Def.v1.Atlas.BooleanFunctions.code.NoiseSensitivity
public import Def.v1.Atlas.BooleanFunctions.code.Talagrand
public import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
public import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part8
public import Def.v1.Atlas.BooleanFunctions.code.Theorems
public import Def.v1.Atlas.BooleanFunctions.code.Lemma26Lec10
open Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredBatch3.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

noncomputable def pBiasedTotalInfluence {n : ℕ} (p : ℝ)
    (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ i : Fin n, (∑ x : Fin n → Bool,
    (∏ j : Fin n, if x j = true then p else (1 - p)) *
    if f x ≠ f (flipCoord x i) then (1 : ℝ) else 0)

noncomputable def criticalProb {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧
    (∑ x : Fin n → Bool,
      (∏ j : Fin n, if x j = true then p else (1 - p)) *
      if f x = true then (1 : ℝ) else 0) ≤ 1 / 2}

end BooleanFourier
