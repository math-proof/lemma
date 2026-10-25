/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Convolution
import Def.v1.Atlas.BooleanFunctions.code.Influence
import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
import Def.v1.Atlas.BooleanFunctions.code.Convolution
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open Finset BigOperators


namespace BooleanFourier

noncomputable def vol {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x = true).card : ℝ) / (2 ^ n : ℝ)

noncomputable def agreementProb {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (1 / (2 : ℝ) ^ n) ^ 2 *
    ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      if boolToReal (f x) * boolToReal (f y) = boolToReal (f (boolMul x y)) then 1 else 0

end BooleanFourier
