/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part2


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


noncomputable def hexGenuineStripMirrorPair :
    HexMirrorBoundaryPair hexGenuineStripDomain hexGenuineStripHeading where
  neg := {hexGenuineStripIncU}
  pos := {hexGenuineStripIncTp}
  disjoint := by
    simp [hexGenuineStripIncU, hexGenuineStripIncTp]
  headNeg := 0
  headPos := 2
  hHeadNeg := by
    intro e he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  hHeadPos := by
    intro e he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  angle := Real.pi / 8
  mass := hexChi ^ 2
  phaseNeg := by
    rw [← hexGenuineStrip_UFiber, ← hexGenuineStrip_core_ups]
    simpa using hexGenuineStrip_corrected_phase_U
  phasePos := by
    rw [← hexGenuineStrip_TpFiber, ← hexGenuineStrip_core_tau]
    exact hexGenuineStrip_corrected_phase_Tp


noncomputable def hexGenuineStripMirrorPairedData :
    HexFiniteStripMirrorPairedData (ι := Fin 1)
      hexGenuineStripBoundaryCore where
  heading := hexGenuineStripHeading
  hgeom := hexGenuineStrip_hgeom
  startIncidence := hexGenuineStripIncA
  start_mid := hexGenuineStrip_mid_A
  start_heading := rfl
  pairs := fun _ => hexGenuineStripMirrorPair
  boundary_partition := by
    rw [hexGenuineStrip_boundaryIncidences]
    ext e
    simp [HexMirrorBoundaryPair.piece, hexGenuineStripMirrorPair]
    aesop
  start_pairs_disjoint := by
    rw [Finset.disjoint_left]
    intro e heA hpairs
    have heq : e = hexGenuineStripIncA := by simpa using heA
    subst e
    simp [HexMirrorBoundaryPair.piece, hexGenuineStripMirrorPair,
      hexGenuineStripIncA, hexGenuineStripIncU,
      hexGenuineStripIncTp] at hpairs
  pairs_disjoint := by
    intro i hi j hj hij
    exact (hij (Subsingleton.elim i j)).elim


end StatMech.Universality
