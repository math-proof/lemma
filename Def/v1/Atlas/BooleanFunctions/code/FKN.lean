/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FKN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
public import Def.v1.Atlas.BooleanFunctions.code.Definitions
public import Mathlib.Tactic

@[expose] public section

open Finset BigOperators


namespace BooleanFourier

noncomputable def fourierWeightAbove {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => k < S.card),
    fourierCoeff f S ^ 2

noncomputable def boolDist {n : ℕ} (f g : (Fin n → Bool) → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) / (2 ^ n : ℝ)

def dictator {n : ℕ} (i : Fin n) : (Fin n → Bool) → Bool :=
  fun x => x i

def negDictator {n : ℕ} (i : Fin n) : (Fin n → Bool) → Bool :=
  fun x => !(x i)


end BooleanFourier
