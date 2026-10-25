/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFinPrefixIndex {N : Nat} (cut : Fin N) (i : Fin cut.val) : Fin N :=
  ⟨i.val, lt_trans i.isLt cut.isLt⟩


def sixVertexFinSuffixIndex {N : Nat} (cut : Fin N)
    (i : Fin (N - cut.val)) : Fin N :=
  ⟨cut.val + i.val, by omega⟩

end
end StatMech.FrontierD
