/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part2


namespace StatMech.FrontierD

noncomputable section

structure SixVertexConfigurationDisjointCapPairedRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  repair : forall source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt,
    Bool → SixVertexDisjointCapUnitRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade
  source_recoverable : forall first second branch,
    sixVertexDisjointCapPhysicalTarget first (repair first branch) =
      sixVertexDisjointCapPhysicalTarget second (repair second branch) →
    first = second
  branch_distinct : forall source,
    sixVertexDisjointCapPhysicalTarget source (repair source false) ≠
      sixVertexDisjointCapPhysicalTarget source (repair source true)


end
end StatMech.FrontierD
