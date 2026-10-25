/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    SixVertexHorizontalPairedBranchResidualGeometricConstruction.toConstruction
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (geometric : SixVertexHorizontalPairedBranchResidualGeometricConstruction
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source branch := (geometric.realization source branch).1
  target_injective source := by
    intro first second heq
    cases first <;> cases second
    · rfl
    · exfalso
      apply geometric.distinct source
      calc
        geometric.targetConfiguration source false =
            sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source false).1 :=
          (geometric.realization source false).2.symm
        _ = sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source true).1 := congrArg _ heq
        _ = geometric.targetConfiguration source true :=
          (geometric.realization source true).2
    · exfalso
      apply geometric.distinct source
      symm
      calc
        geometric.targetConfiguration source true =
            sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source true).1 :=
          (geometric.realization source true).2.symm
        _ = sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source false).1 := congrArg _ heq
        _ = geometric.targetConfiguration source false :=
          (geometric.realization source false).2
    · rfl
  branch_injective branch := by
    intro first second heq
    apply sixVertexHorizontalActualDeficitConfigurationPair_injective
    apply geometric.recoverable branch first second
    calc
      geometric.targetConfiguration first branch =
          sixVertexHorizontalActualSurplusConfigurationPair
            (geometric.realization first branch).1 :=
        (geometric.realization first branch).2.symm
      _ = sixVertexHorizontalActualSurplusConfigurationPair
            (geometric.realization second branch).1 := congrArg _ heq
      _ = geometric.targetConfiguration second branch :=
        (geometric.realization second branch).2
  supported source branch := by
    change SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source).1
      (sixVertexHorizontalActualSurplusConfigurationPair
        (geometric.realization source branch).1).1
    rw [(geometric.realization source branch).2]
    exact geometric.supported source branch


end
end StatMech.FrontierD
