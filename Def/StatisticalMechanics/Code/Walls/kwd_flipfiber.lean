/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

open StatMech.Ising

section FlipFiber

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj]


def flipConfig (s : ConfigSpace V) : ConfigSpace V := fun v => ! s v

end FlipFiber
end Walls
end StatMech
