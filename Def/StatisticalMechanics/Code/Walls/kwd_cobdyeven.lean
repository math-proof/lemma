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
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


def colourDisagrees (c : V → Bool) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => c u ≠ c v, by
    intro a b; exact propext ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩⟩ e

end Coboundary
end Walls
end StatMech
