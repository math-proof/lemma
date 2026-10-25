/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part3
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

def pfdOuterLeafOpenGraph (P : PlanarZ2Subgraph) (F : Set (kwg_Edge P)) :
    SimpleGraph (pfdOuterLeafVertex P) where
  Adj x y := x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y)
  symm := by
    constructor
    rintro x y ⟨hne, e, heF, he⟩
    exact ⟨hne.symm, e, heF, he.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end
end StatMech.FrontierD
