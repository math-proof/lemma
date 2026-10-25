/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section WalkParity

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (δ : Finset (Sym2 V))


def walkPar : {x y : V} → G.Walk x y → Bool
  | _, _, .nil => false
  | _, _, .cons (u := u) (v := v) _ p => (decide (s(u, v) ∈ δ)).xor (walkPar p)

end WalkParity
end StatMech.Walls
