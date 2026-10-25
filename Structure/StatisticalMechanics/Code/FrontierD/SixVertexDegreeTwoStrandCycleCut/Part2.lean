/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut


namespace StatMech.FrontierD

noncomputable section

structure SixVertexDirectedComplementaryArcPair (T : EvenTorus) where
  first : SixVertexDirectedSimpleArc T
  second : SixVertexDirectedSimpleArc T
  first_finish_eq_second_start : first.finish = second.start
  second_finish_eq_first_start : second.finish = first.start
  tail_disjoint : ∀ i j, (first.edge i).tail ≠ (second.edge j).tail
  physical_disjoint : ∀ i j,
    (first.edge i).physical ≠ (second.edge j).physical


end
end StatMech.FrontierD
