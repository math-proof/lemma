/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UncoveredTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Parseval
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Parseval
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Stability
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.NoiseStability
import Def.v1.Atlas.BooleanFunctions.code.Stability
import Def.v1.Atlas.BooleanFunctions.code.Hypercontractivity
open Finset BigOperators


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
