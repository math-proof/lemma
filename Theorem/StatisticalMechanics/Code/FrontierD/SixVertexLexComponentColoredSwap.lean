/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusEdgeMaskVertexMask_eq_true_iff
    {T : EvenTorus} (edgeMask : SixVertexArrows T) (v : T.Vertex) :
    sixVertexTorusEdgeMaskVertexMask edgeMask v = true ↔
      ∃ side : Fin 4,
        sixVertexTorusLocalSwitchMask edgeMask v side = true := by
  simp [sixVertexTorusEdgeMaskVertexMask]

theorem sixVertexTorusLocalSwitchMask_bondMate
    {T : EvenTorus} (edgeMask : SixVertexArrows T)
    (d : SixVertexTorusDart T) :
    sixVertexTorusLocalSwitchMask edgeMask
        (sixVertexTorusDartBondMate T d).1
        (sixVertexTorusDartBondMate T d).2 =
      sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 := by
  rw [sixVertexTorusLocalSwitchMask_apply,
    sixVertexTorusLocalSwitchMask_apply]
  exact congrArg (sixVertexTorusMaskSelects edgeMask)
    (sixVertexTorusDartEdge_bondMate T d)

end
end StatMech.FrontierD
