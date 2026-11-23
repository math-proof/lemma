/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Sensitivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.Influence
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Influence
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Nat

@[expose] public section

namespace BooleanFourier

def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  Finset.card (Finset.filter (fun i => f x ≠ f (flipCoord x i)) Finset.univ)

end BooleanFourier
