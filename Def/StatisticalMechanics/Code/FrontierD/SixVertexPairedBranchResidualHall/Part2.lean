/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalPairedBranchResidualEmbeddings.toConstruction
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexHorizontalPairedBranchResidualEmbeddings
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source branch := embeddings.branch branch source
  target_injective source := by
    intro first second heq
    cases first <;> cases second
    · rfl
    · exact False.elim (embeddings.distinct source heq)
    · exact False.elim (embeddings.distinct source heq.symm)
    · rfl
  branch_injective branch := (embeddings.branch branch).injective
  supported := embeddings.supported

noncomputable def
    SixVertexHorizontalPairedBranchResidualConstruction.inverseBranch
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
      exists branch, construction.target source branch = output}) : Bool :=
  Classical.choose source.2

end
end StatMech.FrontierD
