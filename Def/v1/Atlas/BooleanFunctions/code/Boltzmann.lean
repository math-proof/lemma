/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Boltzmann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Theorems
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Theorems
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog


namespace BooleanFourier

open Finset Real

def restrict {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) :
    (Fin n → Bool) → Bool :=
  fun y => f (Fin.cons b y)

end BooleanFourier
