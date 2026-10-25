/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualDomination
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Universality

noncomputable section

theorem fkSquareActiveRestrictLE_monotone {R N : Nat} (hRN : R ≤ N) :
    Monotone (fkSquareActiveRestrictLE hRN) := by
  intro rho eta hle a
  unfold fkSquareActiveRestrictLE restrictActive FK.boxRestrictLE
  have hedge := fkSquare_innerEdgeLE_mem_edgeSet hRN a
  simp only [extendActive, hedge, dite_true]
  exact hle _

@[simp] theorem fkSquareActiveRestrictLE_faceDual
    {R N : Nat} (hRN : R ≤ N)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    fkSquareActiveRestrictLE hRN (fkSquareFaceDualInnerActive N omega) =
      fkSquareFaceDualInnerActive R omega := by
  funext a
  unfold fkSquareActiveRestrictLE restrictActive FK.boxRestrictLE
  have hedge := fkSquare_innerEdgeLE_mem_edgeSet hRN a
  simp only [extendActive, hedge, dite_true]
  change fci_faceDualConfig omega
        (FK.edgeIncl 2 N (FK.innerEdgeLE 2 hRN a.1)) =
      fci_faceDualConfig omega (FK.edgeIncl 2 R a.1)
  rw [FK.edgeIncl_innerEdgeLE]

@[simp] theorem fkSquareActiveRestrictLE_restrictActive
    {R N : Nat} (hRN : R ≤ N)
    (eta : ConfigSpace (Sym2 (FK.boxVerts 2 N))) :
    fkSquareActiveRestrictLE hRN (restrictActive (FK.boxGraph 2 N) eta) =
      restrictActive (FK.boxGraph 2 R) (FK.boxRestrictLE 2 hRN eta) := by
  funext a
  unfold fkSquareActiveRestrictLE restrictActive FK.boxRestrictLE
  have hedge := fkSquare_innerEdgeLE_mem_edgeSet hRN a
  simp only [extendActive, hedge, dite_true]

end
end StatMech.FrontierD
