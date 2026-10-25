/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectRowZeroVertex (R : FKRectTorus) (x : Fin R.width) : R.Vertex :=
  (x, ⟨0, R.height_pos⟩)

def fkRectRowOneVertex (R : FKRectTorus) (x : Fin R.width) : R.Vertex :=
  (x, ⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩)

def fkRectLastRowVertex (R : FKRectTorus) (x : Fin R.width) : R.Vertex :=
  (x, svFinLast R.height_pos)


def fkRectVerticalSeamEdgeAt (R : FKRectTorus)
    (x : Fin R.width) : R.EdgeIndex :=
  (true, fkRectRowZeroVertex R x)


def fkRectRowZeroAttachmentEdgeAt (R : FKRectTorus)
    (x : Fin R.width) : R.EdgeIndex :=
  (true, fkRectRowOneVertex R x)

end
end StatMech.FrontierD
