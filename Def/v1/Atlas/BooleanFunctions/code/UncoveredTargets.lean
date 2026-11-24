module
public import Def.v1.Atlas.BooleanFunctions.code.Parseval
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Parseval
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Stability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
public import Def.v1.Atlas.BooleanFunctions.code.Stability
public import Def.v1.Atlas.BooleanFunctions.code.Hypercontractivity
open Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

noncomputable def fourierWeightAtLevel {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k),
    (fourierCoeff f S) ^ 2

noncomputable def fourierWeightAtOrAboveLevel {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => k ≤ S.card),
    (fourierCoeff f S) ^ 2

noncomputable def fourierWeightUpToLevel {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k),
    (fourierCoeff f S) ^ 2

end BooleanFourier
