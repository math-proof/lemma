/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part3


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripFourPhaseData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}
  {G : HexRegion} (H : HexFiniteStripFourPhaseData C G)

include H


noncomputable def toHalfRegionAssign : HexRegionAssign D P G where
  heading := H.heading
  hgeom := H.hgeom
  headA := 4
  headL := H.headL
  headTp := H.headTp
  headTm := H.headTm
  headU := H.headU
  hHeadA := H.hHeadA
  hHeadL := H.hHeadL
  hHeadTp := H.hHeadTp
  hHeadTm := H.hHeadTm
  hHeadU := H.hHeadU
  lam := C.lam / 2
  taup := H.taup / 2
  taum := H.taum / 2
  ups := C.ups / 2
  Fa := C.Fa / 2
  projA := by
    have hp := H.projA_unit
    calc
      ((1 / 2 : ℂ) * hexUnit 4) *
            (∑ e ∈ (D.incidences \ P.interior).filter
                (fun e => hexRegionClsInc G D e = 0),
              D.obs (D.mid e.vtx e.edge)) =
          (1 / 2 : ℂ) *
            (hexUnit 4 *
              (∑ e ∈ (D.incidences \ P.interior).filter
                  (fun e => hexRegionClsInc G D e = 0),
                D.obs (D.mid e.vtx e.edge))) := by ring
      _ = (1 / 2 : ℂ) *
          (Complex.I * (((-1 : ℝ) * C.Fa : ℝ) : ℂ)) := by rw [hp]
      _ = Complex.I * (((-1 : ℝ) * (C.Fa / 2) : ℝ) : ℂ) := by
        push_cast
        ring
  projL := hexUnitPhase_half_proj H.headL hexBdryCl C.lam _ H.phaseL
  projTp := hexUnitPhase_half_proj H.headTp hexBdryCt H.taup _ H.phaseTp
  projTm := hexUnitPhase_half_proj H.headTm hexBdryCt H.taum _ H.phaseTm
  projU := by
    simpa using
      (hexUnitPhase_half_proj H.headU 1 C.ups _ (by simpa using H.phaseU))

end HexFiniteStripFourPhaseData
end StatMech.Universality
