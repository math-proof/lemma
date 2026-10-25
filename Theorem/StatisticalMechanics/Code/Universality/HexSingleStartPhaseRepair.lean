/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexProjPhaseClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Structure.StatisticalMechanics.Code.Universality.HexSingleStartPhaseRepair


namespace StatMech.Universality

open Complex

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexSingleStartPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexSingleStartPhaseData D P R)

include H in

@[simp] theorem startFiber_card :
    ((D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0)).card = 1 := by
  rw [H.startFiber]
  simp


theorem eq_startInc_of_mem_startFiber
    (e : HexIncidence V)
    (he : e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0)) :
    e = H.startInc := by
  rw [H.startFiber] at he
  exact Finset.mem_singleton.mp he


theorem heading_eq_four_on_startFiber
    (e : HexIncidence V)
    (he : e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0)) :
    H.heading e.vtx e.edge = 4 := by
  have heq := H.eq_startInc_of_mem_startFiber e he
  subst e
  exact H.startHeading


theorem startProjection :
    ((1 / 2 : ℂ) * hexUnit 4) *
        (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e ↦ hexRegionClsInc R D e = 0),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * (H.Fa / 2) : ℝ) : ℂ) := by
  rw [H.startFiber, Finset.sum_singleton, H.startMid, H.obsStart,
    hpp_alphaDir]
  push_cast
  ring


theorem startProjection_hexChi (hFa : H.Fa = hexChi) :
    ((1 / 2 : ℂ) * hexUnit 4) *
        (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e ↦ hexRegionClsInc R D e = 0),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * (hexChi / 2) : ℝ) : ℂ) := by
  simpa [hFa] using H.startProjection


end HexSingleStartPhaseData
end StatMech.Universality
