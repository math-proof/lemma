/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Structure.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripFourPhaseData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}
  {G : HexRegion} (H : HexFiniteStripFourPhaseData C G)

include H


theorem startFSum_eq_Fa :
    (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0),
      D.obs (D.mid e.vtx e.edge)) = (C.Fa : ℂ) := by
  rw [H.startFiber_singleton, Finset.sum_singleton, H.start_mid, H.start_eq]
  exact C.Fa_eq.symm


theorem startFSum_eq_hexChi :
    (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0),
      D.obs (D.mid e.vtx e.edge)) = (hexChi : ℂ) := by
  rw [H.startFSum_eq_Fa, C.Fa_eq_hexChi]


theorem normalized_startFSum_eq_one :
    (hexChi : ℂ)⁻¹ *
      (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0),
        D.obs (D.mid e.vtx e.edge)) = 1 := by
  rw [H.startFSum_eq_hexChi]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hexChi_pos))


theorem projA_unit :
    hexUnit 4 *
      (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0),
        D.obs (D.mid e.vtx e.edge)) =
      Complex.I * (((-1 : ℝ) * C.Fa : ℝ) : ℂ) := by
  rw [H.startFSum_eq_Fa, hexStart_hexUnit_four]
  push_cast
  ring


theorem normalized_startContribution_eq_neg_one :
    -(hexChi : ℂ)⁻¹ *
      (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0),
        D.obs (D.mid e.vtx e.edge)) = -1 := by
  rw [H.startFSum_eq_hexChi]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hexChi_pos)]


theorem hHeadA : ∀ e ∈ (D.incidences \ P.interior).filter
    (fun e => hexRegionClsInc G D e = 0),
    H.heading e.vtx e.edge = 4 := by
  intro e he
  have he' : e ∈ ({H.startIncidence} : Finset (HexIncidence V)) := by
    rw [← H.startFiber_singleton]
    exact he
  have heq : e = H.startIncidence := by simpa using he'
  subst e
  exact H.start_heading


end HexFiniteStripFourPhaseData
end StatMech.Universality
