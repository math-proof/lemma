/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPhaseTransport.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualPercolation
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.PercoItems
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

theorem fci_faceDualConfig_shift
    (g : Multiplicative (Site 2))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    fci_faceDualConfig (ConfigSpace.shift g omega) =
      ConfigSpace.shift g (fci_faceDualConfig omega) := by
  have hsmul (e : Sym2 (Site 2)) :
      g⁻¹ • e =
        Sym2.map (siteTranslate (Multiplicative.toAdd g⁻¹)) e := by
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [smul_sym2_mk, Sym2.map_mk]
        congr 1 <;> funext i <;>
          simp [smul_site_apply, siteTranslate, add_comm]
  funext e
  simp only [fci_faceDualConfig, ConfigSpace.shift_apply]
  rw [hsmul (fci_faceEdgeEquiv e), hsmul e,
    fci_faceEdgeEquiv_shift]

end
end StatMech.FrontierD
