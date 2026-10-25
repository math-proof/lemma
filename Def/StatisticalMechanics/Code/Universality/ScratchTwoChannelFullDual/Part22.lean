/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelIndexedRandomGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') where
  Adj x y := x ≠ y ∧ ∃ f,
    rlc_twoChannelIndexedOuterEdge gamma gamma' f = s(x, y)
  symm := by
    constructor
    rintro x y ⟨hne, f, hf⟩
    exact ⟨hne.symm, f, hf.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end
end StatMech.Universality
