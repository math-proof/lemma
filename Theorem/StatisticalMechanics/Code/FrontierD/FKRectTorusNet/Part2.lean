/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem not_FKRectWindingIndependent_self (u : Int × Int) :
    ¬ FKRectWindingIndependent u u := by
  simp [FKRectWindingIndependent, mul_comm]


theorem fkRect_diagonal_winding_not_independent :
    ¬ FKRectWindingIndependent ((1, 1) : Int × Int) (1, 1) := by
  exact not_FKRectWindingIndependent_self _


end
end StatMech.FrontierD
