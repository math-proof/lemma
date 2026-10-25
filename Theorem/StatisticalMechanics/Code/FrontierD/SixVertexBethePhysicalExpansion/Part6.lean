/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexBetheWordMLSet {n : Nat}
    (w : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheWordMLSet w ↔
      i ∉ w ∧ finRotate (n + 1) i ∈ w := by
  simp [sixVertexBetheWordMLSet]

theorem sixVertexBetheWordMLSet_noAdjacent {n : Nat}
    (w : Finset (Fin (n + 1))) :
    SixVertexBetheNoAdjacent (sixVertexBetheWordMLSet w) := by
  intro i hi hinext
  have hi' := (mem_sixVertexBetheWordMLSet w i).mp hi
  have hn' := (mem_sixVertexBetheWordMLSet w
    (finRotate (n + 1) i)).mp hinext
  exact hn'.1 hi'.2


end
end StatMech.FrontierD
