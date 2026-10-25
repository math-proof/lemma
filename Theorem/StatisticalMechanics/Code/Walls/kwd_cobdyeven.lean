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
import Def.StatisticalMechanics.Code.Walls.kwd_cobdyeven
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


omit [DecidableEq V] in
@[simp] theorem colourDisagrees_mk (c : V → Bool) (u v : V) :
    colourDisagrees c s(u, v) ↔ c u ≠ c v := by
  unfold colourDisagrees; rw [Sym2.lift_mk]

end Coboundary
end Walls
end StatMech
