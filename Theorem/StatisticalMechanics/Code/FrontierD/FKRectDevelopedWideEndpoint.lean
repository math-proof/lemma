/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem mem_fkRectDevelopedThreeByOneVerticalEndpointPairs
    (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n ↔
      p.1.1 1 = 0 ∧ p.2.1 1 = n := by
  classical
  unfold fkRectDevelopedThreeByOneVerticalEndpointPairs
  simp


end
end StatMech.FrontierD
