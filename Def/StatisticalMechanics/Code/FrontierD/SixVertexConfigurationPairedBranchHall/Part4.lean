/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def SixVertexConfigurationPairedBranchEmbeddings.inverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade) :
    {source : SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade //
      SixVertexConfigurationPairedBranchRelated embeddings source target} ↪
        Fin 2 where
  toFun source := finTwoEquiv.symm
    (embeddings.inverseBranch target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : embeddings.inverseBranch target first =
        embeddings.inverseBranch target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply (embeddings.branch
      (embeddings.inverseBranch target first)).injective
    calc
      embeddings.branch (embeddings.inverseBranch target first) first.1 =
          target := embeddings.branch_inverseBranch target first
      _ = embeddings.branch (embeddings.inverseBranch target second) second.1 :=
        (embeddings.branch_inverseBranch target second).symm
      _ = embeddings.branch (embeddings.inverseBranch target first) second.1 :=
        by rw [hbranch]

end
end StatMech.FrontierD
