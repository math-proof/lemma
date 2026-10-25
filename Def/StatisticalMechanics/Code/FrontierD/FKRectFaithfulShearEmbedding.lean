/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDiagonalShearSubdivision.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectFaithfulShearPair (p : Int × Int) : Int × Int :=
  (2 * (p.1 + p.2), 2 * (p.1 - p.2))


def fkRectPairSite (p : Int × Int) : Site 2 := ![p.1, p.2]


def fkRectFaithfulShearPoint (p : Int × Int) : Site 2 :=
  fkRectPairSite (fkRectFaithfulShearPair p)

end
end StatMech.FrontierD
