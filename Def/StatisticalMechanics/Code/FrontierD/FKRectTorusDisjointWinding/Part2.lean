/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def FKRectIntegralDartListSupportedOn (R : FKRectTorus)
    (l : List FKRectIntegralSquareDart) (S : R.Vertex → Prop) : Prop :=
  ∀ d ∈ l,
    S (fkRectSquareRepresentativeVertex R d.1) ∧
      S (fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d))

end
end StatMech.FrontierD
