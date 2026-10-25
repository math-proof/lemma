/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CriticalFreeShellSummability
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

noncomputable section

def inverseFaceDualConfig (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => !(omega (fci_faceEdgeEquiv.symm e))


end
end StatMech.FrontierD
