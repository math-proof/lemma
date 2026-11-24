module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

section Handshake

variable {V : Type*} (Gp : SimpleGraph V) (s : ConfigSpace V)


def walkDis : {x y : V} → Gp.Walk x y → ℕ
  | _, _, .nil => 0
  | _, _, .cons (u := u) (v := v) _ p => (if s u ≠ s v then 1 else 0) + walkDis p


end Handshake
end Ising
end StatMech
