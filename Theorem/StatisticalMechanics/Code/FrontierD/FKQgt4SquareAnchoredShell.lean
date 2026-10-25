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
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

noncomputable section

theorem measurable_inverseFaceDualConfig :
    Measurable
      (inverseFaceDualConfig :
        ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
  let reindex := Equiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv
  have hreindex : Measurable reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun _ => Bool) fci_faceEdgeEquiv).measurable
  have hcomp := measurable_complement.comp hreindex
  convert hcomp using 1 <;> funext omega e <;>
    simp [inverseFaceDualConfig, reindex, Equiv.piCongrLeft_apply]

@[simp] theorem fci_faceDualConfig_inverseFaceDualConfig
    (omega : ConfigSpace (Sym2 (Site 2))) :
    fci_faceDualConfig (inverseFaceDualConfig omega) = omega := by
  funext e
  simp [fci_faceDualConfig, inverseFaceDualConfig]

@[simp] theorem inverseFaceDualConfig_fci_faceDualConfig
    (eta : ConfigSpace (Sym2 (Site 2))) :
    inverseFaceDualConfig (fci_faceDualConfig eta) = eta := by
  funext e
  simp [fci_faceDualConfig, inverseFaceDualConfig]


end
end StatMech.FrontierD
