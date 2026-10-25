/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectInsertEdgeList_eq_union_toFinset
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex) :
    fkRectInsertEdgeList R F es = F ∪ es.toFinset := by
  classical
  induction es generalizing F with
  | nil => simp [fkRectInsertEdgeList]
  | cons e es ih =>
      rw [fkRectInsertEdgeList, ih]
      ext a
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto


end
end StatMech.FrontierD
