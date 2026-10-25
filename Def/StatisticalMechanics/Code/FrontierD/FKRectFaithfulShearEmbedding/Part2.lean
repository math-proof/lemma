/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDiagonalShearSubdivision.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearEmbedding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectFaithfulShearDartRoute (d : FKRectIntegralSquareDart) :
    List (Int × Int) :=
  let a := fkRectFaithfulShearPair d.1
  match d.2 with
  | 0 => [a, (a.1 + 1, a.2), (a.1 + 1, a.2 + 1),
      (a.1 + 1, a.2 + 2), (a.1 + 2, a.2 + 2)]
  | 1 => [a, (a.1, a.2 - 1), (a.1 + 1, a.2 - 1),
      (a.1 + 2, a.2 - 1), (a.1 + 2, a.2 - 2)]
  | 2 => [a, (a.1 - 1, a.2), (a.1 - 1, a.2 - 1),
      (a.1 - 1, a.2 - 2), (a.1 - 2, a.2 - 2)]
  | 3 => [a, (a.1, a.2 + 1), (a.1 - 1, a.2 + 1),
      (a.1 - 2, a.2 + 1), (a.1 - 2, a.2 + 2)]


def FKRectIntegralSquareDartsIncident
    (d e : FKRectIntegralSquareDart) : Prop :=
  d.1 = e.1 ∨ d.1 = fkRectIntegralSquareDartEnd e ∨
    fkRectIntegralSquareDartEnd d = e.1 ∨
      fkRectIntegralSquareDartEnd d = fkRectIntegralSquareDartEnd e

end
end StatMech.FrontierD
