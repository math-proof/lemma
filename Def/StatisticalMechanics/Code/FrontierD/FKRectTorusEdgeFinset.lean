/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectOpenEdges (R : FKRectTorus) (omega : R.Configuration) :
    Finset R.EdgeIndex :=
  Finset.univ.filter fun a => omega a = true


def fkRectConfigurationOfEdges (R : FKRectTorus)
    (F : Finset R.EdgeIndex) : R.Configuration :=
  fun a => decide (a ∈ F)

end
end StatMech.FrontierD
