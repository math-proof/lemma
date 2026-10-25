/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Parseval
import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Def.v1.Atlas.BooleanFunctions.code.Parseval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff
open Finset BigOperators


namespace BooleanFourier

open scoped symmDiff

noncomputable def influenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool,
    ((f x - f (flipAt i x)) / 2) ^ 2

noncomputable def totalInfluenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ i : Fin n, influenceReal f i

noncomputable def varianceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (· ≠ ∅), fourierCoeff f S ^ 2

end BooleanFourier
