/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Sensitivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Nat


namespace BooleanFourier

def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  Finset.card (Finset.filter (fun i => f x ≠ f (flipCoord x i)) Finset.univ)

end BooleanFourier
