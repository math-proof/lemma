/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section CutParity

variable {V : Type*} [DecidableEq V] (Gp : SimpleGraph V) (δ : Finset (Sym2 V))


def walkParity : {x y : V} → Gp.Walk x y → Bool
  | _, _, .nil => false
  | _, _, .cons (u := u) (v := v) _ p => (decide (s(u, v) ∈ δ)).xor (walkParity p)

end CutParity
end Ising
end StatMech
