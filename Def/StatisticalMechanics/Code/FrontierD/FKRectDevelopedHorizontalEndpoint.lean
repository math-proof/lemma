/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectDevelopedThreeByOneHorizontalEndpointPairs (n : Nat) :
    Finset ((fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) := by
  classical
  letI : Fintype (fkRectDevelopedThreeByOneRect n) := by
    rw [fkRectDevelopedThreeByOneRect]
    exact (rect_finite 0 (3 * (n : Int)) 0 n).fintype
  exact Finset.univ.filter fun p =>
    p.1.1 0 = 0 ∧ p.2.1 0 = 3 * (n : Int)

end
end StatMech.FrontierD
