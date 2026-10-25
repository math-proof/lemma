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
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_centralFaceReachSet_openWalk_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u v : RlcConnectorVertex n}
    (hu : (u : Site 2) ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (w : (openSubgraphInduce 2
      (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
      (rect (-2 * n) (2 * n) (-n) n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈
        rlc_connectorCentralFaceReachSet gamma gamma' rho,
      ((hypercubicLattice 2).induce
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)).Adj
          (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈
          rlc_connectorCentralFaceReachSet gamma gamma' rho :=
        rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hu b.2
          habOpen.1 habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habReach : ((hypercubicLattice 2).induce
          (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := habOpen.1
      exact ⟨hc, habReach.reachable.trans hbc⟩


theorem rlc_connectorCentralFaceReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
    ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hu0 := hu
  have hv0 := hv
  obtain ⟨huBox, huSource⟩ := hu
  obtain ⟨hvBox, hvSource⟩ := hv
  have hsource : (rlc_connectorRightAnchor gamma : Site 2) ∈
      rlc_connectorCentralFaceReachSet gamma gamma' rho :=
    ⟨(rlc_connectorRightAnchor gamma).2, Reachable.refl _⟩
  obtain ⟨hu', huLift⟩ := rlc_centralFaceReachSet_openWalk_lift
    gamma gamma' rho hu0 huSource.some.reverse
  obtain ⟨hv', hvLift⟩ := rlc_centralFaceReachSet_openWalk_lift
    gamma gamma' rho hsource hvSource.some
  have huEq :
      (⟨(rlc_connectorRightAnchor gamma : Site 2), hu'⟩ :
        rlc_connectorCentralFaceReachSet gamma gamma' rho) =
      ⟨(rlc_connectorRightAnchor gamma : Site 2), hsource⟩ := rfl
  have hvEq :
      (⟨v, hv'⟩ : rlc_connectorCentralFaceReachSet gamma gamma' rho) =
      ⟨v, hv0⟩ := rfl
  rw [huEq] at huLift
  rw [hvEq] at hvLift
  exact huLift.trans hvLift

theorem rlc_connectorCentralFaceReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {u v : Site 2}
    (hu : u ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
    (latticeMinusBarrier
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)) →g
      latticeMinusBarrier
        (rlc_connectorCentralFaceReachSet gamma gamma' rho) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorCentralFaceReachSet_reachable
    gamma gamma' rho hu hv).map hom
  simpa [hom] using h


end
end StatMech.Universality
