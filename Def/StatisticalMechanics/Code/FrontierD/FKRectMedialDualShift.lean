/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3


namespace StatMech.FrontierD

def fkRectMedialDualShiftVertex
    (R : FKRectTorus) (v : R.medialTorus.Vertex) : R.medialTorus.Vertex :=
  (SixVertexArrows.cyclicPred R.medialTorus.width_pos v.1, v.2)


def fkRectMedialDualShiftDart
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    FKMedialDart R.medialTorus :=
  (fkRectMedialDualShiftVertex R d.1, d.2)


def fkRectMedialDualUnshiftVertex
    (R : FKRectTorus) (v : R.medialTorus.Vertex) : R.medialTorus.Vertex :=
  (finitePeriodicSucc R.medialTorus.width_pos v.1, v.2)


def fkRectMedialDualUnshiftDart
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    FKMedialDart R.medialTorus :=
  (fkRectMedialDualUnshiftVertex R d.1, d.2)

end StatMech.FrontierD
