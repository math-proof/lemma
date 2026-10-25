/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoverageGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareHoleFill.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.Universality

noncomputable section

def squareDualClusterCoverage
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) : Set (Site 2) :=
  ⋃ x ∈ box 2 n, cluster 2 (fci_faceDualConfig omega) x

end
end StatMech.FrontierD
