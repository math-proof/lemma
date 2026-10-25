/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

theorem fci_faceEdgeEquiv_symm_mk_of_adj
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    fci_faceEdgeEquiv.symm s(x, y) = flankFaces x y := by
  obtain ⟨f, g, hfg, hfgAdj⟩ := flankFaces_latAdj hxy
  apply fci_faceEdgeEquiv.injective
  rw [fci_faceEdgeEquiv.apply_symm_apply, hfg,
    fci_faceEdgeEquiv_mk_of_adj hfgAdj, ← symPrimal_eq_shared hfgAdj,
    ← symPrimalSym_mk, ← hfg, symPrimalSym_flankFaces hxy]


theorem inverseFaceDualConfig_eq_faceDual_doubleDualShift
    (omega : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    inverseFaceDualConfig omega s(x, y) =
      fci_faceDualConfig omega
        s(phb_doubleDualShift x, phb_doubleDualShift y) := by
  rw [inverseFaceDualConfig, fci_faceDualConfig,
    fci_faceEdgeEquiv_symm_mk_of_adj hxy,
    fci_faceEdgeEquiv_mk_of_adj (phb_doubleDualShift_latAdj.mpr hxy),
    phb_sharedPrimalEdge_shift_eq_flankFaces hxy]


end
end StatMech.FrontierD
