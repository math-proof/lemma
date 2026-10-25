/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalPairedBranchResidualConstruction.target_inverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)
    (source : {source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
      exists branch, construction.target source branch = output}) :
    construction.target source.1
        (construction.inverseBranch output source) = output :=
  Classical.choose_spec source.2


end
end StatMech.FrontierD
