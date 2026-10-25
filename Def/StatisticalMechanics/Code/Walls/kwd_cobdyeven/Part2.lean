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
import Instance.StatisticalMechanics.Code.Walls.kwd_cobdyeven
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


variable [Fintype V] [DecidableRel Gp.Adj]


noncomputable def coboundary (Gp : SimpleGraph V) [Fintype V] [DecidableRel Gp.Adj]
    (c : V → Bool) : Finset (Sym2 V) :=
  Gp.edgeFinset.filter (colourDisagrees c)

end Coboundary
end Walls
end StatMech
