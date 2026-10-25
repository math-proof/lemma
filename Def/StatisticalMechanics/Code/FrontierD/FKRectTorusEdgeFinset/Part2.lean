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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectConfigurationEdgeFinsetEquiv (R : FKRectTorus) :
    R.Configuration ≃ Finset R.EdgeIndex where
  toFun := fkRectOpenEdges R
  invFun := fkRectConfigurationOfEdges R
  left_inv := fkRectConfigurationOfEdges_openEdges R
  right_inv := fkRectOpenEdges_configurationOfEdges R

end
end StatMech.FrontierD
