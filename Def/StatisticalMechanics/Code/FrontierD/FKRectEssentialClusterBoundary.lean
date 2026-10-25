/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectClusterBoundaryDarts
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    Finset (FKMedialDart R.medialTorus) :=
  Finset.univ.filter fun d =>
    (fkRectOpenGraph R omega).Reachable x
      (fkRectMedialDartPrimalLabel R d)

end
end StatMech.FrontierD
