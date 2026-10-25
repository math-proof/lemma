/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawHorizontalCrossingRepresentative_component
    (R : FKRectTorus) (eta : R.Configuration)
    (C : {C : (fkRectOpenGraph R eta).ConnectedComponent //
      FKRectRawHorizontalCrossingComponent R eta C}) :
    (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawHorizontalCrossingRepresentative R eta C) = C.1 :=
  Classical.choose_spec C.2.1

theorem fkRectRawHorizontalCrossingRepresentative_source
    (R : FKRectTorus) (eta : R.Configuration)
    (C : {C : (fkRectOpenGraph R eta).ConnectedComponent //
      FKRectRawHorizontalCrossingComponent R eta C}) :
    FKRectRawHorizontalCrossingSource R eta
      (fkRectRawHorizontalCrossingRepresentative R eta C) := by
  rcases C.2.2 with ⟨z, hz⟩
  refine ⟨z, SimpleGraph.ConnectedComponent.exact ?_⟩
  exact (fkRectRawHorizontalCrossingRepresentative_component R eta C).trans
    hz.symm

theorem fkRectRawHorizontalCrossingRepresentative_injective
    (R : FKRectTorus) (eta : R.Configuration) :
    Function.Injective
      (fkRectRawHorizontalCrossingRepresentative R eta) := by
  intro C D hCD
  apply Subtype.ext
  exact (fkRectRawHorizontalCrossingRepresentative_component R eta C).symm.trans
    ((congrArg
      (fun y => (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectLeftColumn R, y)) hCD).trans
      (fkRectRawHorizontalCrossingRepresentative_component R eta D))


end
end StatMech.FrontierD
