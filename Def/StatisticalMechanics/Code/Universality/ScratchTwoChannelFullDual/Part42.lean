/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part33
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullMaxTraceKernelWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x =
      rlc_twoChannelFullMaxInnerTraceRep gamma gamma' y
  symm := by
    constructor
    rintro x y ⟨hne, hrep⟩
    exact ⟨hne.symm, hrep.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end
end StatMech.Universality
