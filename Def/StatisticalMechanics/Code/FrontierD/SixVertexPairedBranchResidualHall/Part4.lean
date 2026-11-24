module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalPairedBranchResidualAtlases
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade : Nat × Nat, Nonempty
    (SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)


def SixVertexHorizontalPairedBranchResidualConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade : Nat × Nat, Nonempty
    (SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade)

end
end StatMech.FrontierD
