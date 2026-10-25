/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem sixVertexCanonicalOddActualHalfProduct_pos
    {c : Real} (hc : 2 < c) (s k : Nat) :
    0 < sixVertexCanonicalOddActualHalfProduct hc s k := by
  unfold sixVertexCanonicalOddActualHalfProduct
  exact Finset.prod_pos fun j hj => div_pos
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))

theorem sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    sixVertexCanonicalOddZeroModeWallisCorrection hc s k =
      Real.log
        ((sixVertexZeroPhaseBethePrefactor c
            (sixVertexFourWidth (2 * s + 1) k)
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
            (sixVertexOddCentralIndex (s + k + 1)) / 2) *
          sixVertexCanonicalOddActualHalfProduct hc s k ^ 2) := by
  let P := sixVertexZeroPhaseBethePrefactor c
    (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
    (sixVertexOddCentralIndex (s + k + 1))
  have hcentral :=
    sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
      hc s k hfixed
  have hP : 0 < P := sixVertexZeroPhaseBethePrefactor_pos hc
    (by unfold sixVertexFourWidth; omega)
    _ _ hcentral
  have hterm (j : Fin (s + k + 1)) :
      0 < ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
      ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖ :=
    div_pos (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
  have hlogProd : Real.log (sixVertexCanonicalOddActualHalfProduct hc s k) =
      ∑ j : Fin (s + k + 1),
        Real.log (‖sixVertexBetheM c (sixVertexBethePhase
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
          ‖sixVertexBetheM c (sixVertexBethePhase
            (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖) := by
    unfold sixVertexCanonicalOddActualHalfProduct
    rw [Real.log_prod (fun j hj => (hterm j).ne')]
  unfold sixVertexCanonicalOddZeroModeWallisCorrection
    sixVertexBetheLogObservable
  rw [Real.log_mul (div_ne_zero hP.ne' (by norm_num))
      (pow_ne_zero 2
        (sixVertexCanonicalOddActualHalfProduct_pos hc s k).ne'),
    Real.log_div hP.ne' (by norm_num : (2 : Real) ≠ 0),
    Real.log_pow, hlogProd]
  simp_rw [Real.log_div
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne'
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne']
  ring

end
end StatMech.FrontierD
