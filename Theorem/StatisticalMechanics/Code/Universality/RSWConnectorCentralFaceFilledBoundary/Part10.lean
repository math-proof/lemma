/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_reflectedFilledCut_incident_component_out_mem_interior {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
    (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho)
    {C : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
    (hinc : Ising.kwg_incidentMod2 C
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
    C.out ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
  obtain ⟨f, g, hfg, heEmbedded⟩ :=
    rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier
      gamma gamma' rho e heCut
  have hrefAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp hfg.1
  have heCarrier :=
    rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents
      hrefAdj e heEmbedded
  rw [heCarrier, Ising.kwg_incidentMod2_mk] at hinc
  obtain ⟨hfInt, hgInt⟩ :=
    rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
      hn gamma gamma' rho hfg
  rcases hinc with hinc | hinc
  · have hout : C.out = rlc_dualReflect f := by
      symm
      apply rlc_crossedBox_interiorFace_component_singleton hfInt
      exact hinc.1.trans C.out_eq.symm
    simpa [hout] using hfInt
  · have hout : C.out = rlc_dualReflect g := by
      symm
      apply rlc_crossedBox_interiorFace_component_singleton hgInt
      exact hinc.1.trans C.out_eq.symm
    simpa [hout] using hgInt


end
end StatMech.Universality
