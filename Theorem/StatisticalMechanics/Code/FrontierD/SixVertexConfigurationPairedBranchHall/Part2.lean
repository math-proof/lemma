/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexConfigurationPairedBranchEmbeddings.branch_inverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade)
    (source : {source : SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade //
      SixVertexConfigurationPairedBranchRelated embeddings source target}) :
    embeddings.branch (embeddings.inverseBranch target source) source.1 =
      target :=
  Classical.choose_spec source.2

end
end StatMech.FrontierD
