/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABCouplingReindex.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem abfaLiftCoupling_some_some (J : Sym2 V → ℝ) (x y : V) :
    abfaLiftCoupling G J s(some x, some y) =
      if s(x, y) ∈ G.edgeFinset then J s(x, y) else 0 := rfl

@[simp] theorem abfaLiftCoupling_some_none (J : Sym2 V → ℝ) (x : V) :
    abfaLiftCoupling G J s(some x, none) = 0 := rfl


end Sharpness
end StatMech
