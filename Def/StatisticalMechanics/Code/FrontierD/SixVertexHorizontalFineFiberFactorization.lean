/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalBoundedSingleRowProfile
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalBoundedSingleRowProfile T :=
  fun j =>
    (⟨sixVertexHorizontalRowNontransitionCount horizontal j,
      Nat.lt_succ_of_le
        (sixVertexHorizontalRowNontransitionCount_le_width horizontal j)⟩,
     ⟨sixVertexHorizontalRowZeroCount horizontal j,
      Nat.lt_succ_of_le
        (sixVertexHorizontalRowZeroCount_le_width horizontal j)⟩)


def sixVertexHorizontalAddSingleRowProfiles
    {T : EvenTorus}
    (first second : SixVertexHorizontalBoundedSingleRowProfile T) :
    SixVertexHorizontalBoundedFineRowProfile T :=
  fun j =>
    (⟨(first j).1.val + (second j).1.val, by
        have hfirst := (first j).1.isLt
        have hsecond := (second j).1.isLt
        omega⟩,
     ⟨(first j).2.val + (second j).2.val, by
        have hfirst := (first j).2.isLt
        have hsecond := (second j).2.isLt
        omega⟩)

end
end StatMech.FrontierD
