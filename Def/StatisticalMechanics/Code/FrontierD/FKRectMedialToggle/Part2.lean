/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeInsertion
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle
open Finset


namespace StatMech.FrontierD

def fkRectMedialVertexOfEdge (R : FKRectTorus) (e : R.EdgeIndex) :
    R.medialTorus.Vertex :=
  (fkRectTorusMedialEdgeEquiv R).symm e

end StatMech.FrontierD
