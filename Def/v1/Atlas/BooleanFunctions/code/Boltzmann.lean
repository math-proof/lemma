module
public import Def.v1.Atlas.BooleanFunctions.code.Theorems
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Theorems
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Boltzmann.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

open Finset Real

def restrict {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) :
    (Fin n → Bool) → Bool :=
  fun y => f (Fin.cons b y)

end BooleanFourier
