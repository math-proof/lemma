/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKFiniteConnectionApproximation
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteProductExceptions


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation Filter Topology

noncomputable section

def fkRectRightBandVertexAtRow
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width) (hx : cut <= x.val)
    (r : Nat) (hr : 1 <= r ∧ r <= R.height - 1) :
    FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
  ⟨(x, ⟨r, by omega⟩), hx, hr⟩


end
end StatMech.FrontierD
