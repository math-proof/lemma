/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Walls.kwd_cobdyeven
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


instance (c : V → Bool) (e : Sym2 V) : Decidable (colourDisagrees c e) :=
  Sym2.recOnSubsingleton e (fun a b => by
    change Decidable (Sym2.lift _ s(a, b))
    rw [Sym2.lift_mk]; infer_instance)

end Coboundary
end Walls
end StatMech
