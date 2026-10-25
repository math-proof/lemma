/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part9
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

noncomputable def crr_cutFaceHom
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    Ising.kwg_deleteVertexGraph
        (Ising.kwg_faceSupportGraph
          (fun e : ↑(crr_boxRCut omega n) =>
            Ising.kwg_dualEnds (crr_boxPlanar n) e.1))
        ((whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk ![-1, -1]) →g
      crr_LRFaceGraph omega n where
  toFun C := crr_boxFaceRep n C
  map_rel' := by
    intro C D hCD
    obtain ⟨hCDsupp, hCout, hDout⟩ := hCD
    obtain ⟨hCDne, e, heEnds⟩ := hCDsupp
    have hecut : e.1 ∈ crr_boxRCut omega n := e.2
    have hflank : (crr_LRFaceGraph omega n).Adj
        (Ising.kwg_flankLeft (crr_boxPlanar n) e.1)
        (Ising.kwg_flankRight (crr_boxPlanar n) e.1) := by
      apply crr_cutEdge_flanks_LRAdj omega n e.1
      exact hecut
    have hflInt : Ising.kwg_flankLeft (crr_boxPlanar n) e.1 ∈
        rect 0 (n - 1) 0 (n - 1) := by
      apply crr_nonOuter_flank_interior e.1 (Or.inl rfl)
      intro hout
      unfold Ising.kwg_dualEnds at heEnds
      rw [Sym2.eq_iff] at heEnds
      rcases heEnds with ⟨hLC, _⟩ | ⟨hLD, _⟩
      · exact hCout (hLC.symm.trans hout)
      · exact hDout (hLD.symm.trans hout)
    have hfrInt : Ising.kwg_flankRight (crr_boxPlanar n) e.1 ∈
        rect 0 (n - 1) 0 (n - 1) := by
      apply crr_nonOuter_flank_interior e.1 (Or.inr rfl)
      intro hout
      unfold Ising.kwg_dualEnds at heEnds
      rw [Sym2.eq_iff] at heEnds
      rcases heEnds with ⟨_, hRD⟩ | ⟨_, hRC⟩
      · exact hDout (hRD.symm.trans hout)
      · exact hCout (hRC.symm.trans hout)
    unfold Ising.kwg_dualEnds at heEnds
    rw [Sym2.eq_iff] at heEnds
    rcases heEnds with ⟨hLC, hRD⟩ | ⟨hLD, hRC⟩
    · have hrepL : crr_boxFaceRep n C = Ising.kwg_flankLeft (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hflInt
        rw [crr_boxFaceRep_component, hLC]
      have hrepR : crr_boxFaceRep n D = Ising.kwg_flankRight (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hfrInt
        rw [crr_boxFaceRep_component, hRD]
      simpa [hrepL, hrepR] using hflank
    · have hrepL : crr_boxFaceRep n D = Ising.kwg_flankLeft (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hflInt
        rw [crr_boxFaceRep_component, hLD]
      have hrepR : crr_boxFaceRep n C = Ising.kwg_flankRight (crr_boxPlanar n) e.1 := by
        symm
        apply crr_whb_box_component_singleton hfrInt
        rw [crr_boxFaceRep_component, hRC]
      simpa [hrepL, hrepR] using hflank.symm


end Universality
end StatMech
