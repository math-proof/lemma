/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectHasNet (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∃ x : R.Vertex,
    ∃ p q : (fkRectOpenGraph R omega).Walk x x,
      FKRectWindingIndependent
        (fkRectWalkWinding R p) (fkRectWalkWinding R q)


def fkRectNetIndicator (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  by
    classical
    exact if FKRectHasNet R omega then 1 else 0

end
end StatMech.FrontierD
