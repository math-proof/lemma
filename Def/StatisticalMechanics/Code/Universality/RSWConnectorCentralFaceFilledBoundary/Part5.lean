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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_reflectedFilledBoundaryGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (Site 2) where
  Adj x y := (faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
      (rlc_dualReflect.symm x) (rlc_dualReflect.symm y)
  symm := ⟨fun _ _ hxy => hxy.symm⟩
  loopless := ⟨fun _ hxx => hxx.ne rfl⟩


noncomputable def rlc_reflectedCutSupportHom {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)))
    (hS : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho) :
    Ising.kwg_faceSupportGraph
        (fun e : ↑S => Ising.kwg_dualEnds
          (rlc_connectorCrossedBoxPlanar n) e.1) →g
      rlc_reflectedFilledBoundaryGraph gamma gamma' rho where
  toFun C := C.out
  map_rel' := by
    intro C D hCD
    obtain ⟨_hCDne, e, heEnds⟩ := hCD
    have heCut : e.1 ∈
        rlc_connectorReflectedFilledCut gamma gamma' rho := hS e.2
    obtain ⟨f, g, hfg, heEmbedded⟩ :=
      rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier
        gamma gamma' rho e.1 heCut
    have hrefAdj : (hypercubicLattice 2).Adj
        (rlc_dualReflect f) (rlc_dualReflect g) :=
      (rlc_adj_dualReflect f g).mp hfg.1
    have heCarrier : Ising.kwg_dualEnds
        (rlc_connectorCrossedBoxPlanar n) e.1 =
        s((whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect f),
          (whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect g)) := by
      let P := rlc_connectorCrossedBoxPlanar n
      have hpair : s(Ising.kwg_flankLeft P e.1,
          Ising.kwg_flankRight P e.1) =
          s(rlc_dualReflect f, rlc_dualReflect g) :=
        (jce_sharedPrimalEdge_inj (Ising.kwg_flanks_adj P e.1)
          hrefAdj).mpr ((Ising.kwg_flanks_shared P e.1).trans heEmbedded)
      unfold Ising.kwg_dualEnds
      rw [Sym2.eq_iff] at hpair ⊢
      rcases hpair with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact Or.inl ⟨congrArg _ hleft, congrArg _ hright⟩
      · exact Or.inr ⟨congrArg _ hleft, congrArg _ hright⟩
    have hpair : s(C, D) =
        s((whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect f),
          (whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
              (rlc_dualReflect g)) := heEnds.symm.trans heCarrier
    obtain ⟨hfInt, hgInt⟩ :=
      rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
        hn gamma gamma' rho hfg
    have rep_eq {A : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
        {x : Site 2}
        (hxInt : x ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1))
        (hxA : (whb_faceRegion
            (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk x = A) :
        A.out = x := by
      symm
      apply rlc_crossedBox_interiorFace_component_singleton hxInt
      exact hxA.trans A.out_eq.symm
    rw [Sym2.eq_iff] at hpair
    rcases hpair with ⟨hCf, hDg⟩ | ⟨hCg, hDf⟩
    · have hC : C.out = rlc_dualReflect f := rep_eq hfInt hCf.symm
      have hD : D.out = rlc_dualReflect g := rep_eq hgInt hDg.symm
      change (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
          (rlc_dualReflect.symm C.out) (rlc_dualReflect.symm D.out)
      rw [hC, hD, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hfg
    · have hC : C.out = rlc_dualReflect g := rep_eq hgInt hCg.symm
      have hD : D.out = rlc_dualReflect f := rep_eq hfInt hDf.symm
      change (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj
          (rlc_dualReflect.symm C.out) (rlc_dualReflect.symm D.out)
      rw [hC, hD, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hfg.symm


end
end StatMech.Universality
