/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section ReachRegion

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


def primalMinus (Gp : SimpleGraph V) (δ : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := Gp.Adj x y ∧ s(x, y) ∉ δ
  symm := by
    constructor
    intro x y ⟨hadj, hbd⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => Gp.irrefl h.1⟩

end ReachRegion
end Ising
end StatMech
