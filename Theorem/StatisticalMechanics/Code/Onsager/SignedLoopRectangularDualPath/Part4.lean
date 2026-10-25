/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part6
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

theorem coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    (ons_sourceX (ons_rectDualGraph M N)
        {path.source, path.target} x : Complex) ^ 2 =
      (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathDefectKWDet embedding path x := by
  exact coe_ons_sourceX_sq_eq_defect_kwDet
    (ons_rectDualGraph M N) embedding
    (ons_rectDualPathDefect_subset_edgeFinset path)
    (ons_rectDualPathDefect_hasOddBoundary path) hx


theorem ons_rectDualPath_defectKWDet_eq_signedLoopObservable
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    ons_rectDualPathDefectKWDet embedding path x =
      ons_rectDualPathSignedLoopObservable path x := by
  have hraw := coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet
    embedding path hx
  have hxc : (x : Complex) ≠ 0 := by exact_mod_cast hx
  unfold ons_rectDualPathSignedLoopObservable
  rw [hraw]
  field_simp [hxc]


theorem coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) {beta : Real} (hbeta : 0 < beta) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((Real.tanh beta : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathDefectKWDet embedding path (Real.tanh beta)) /
        ons_rectDualKWDet embedding (Real.tanh beta) := by
  have htanh : Real.tanh beta ≠ 0 := by
    intro hzero
    apply hbeta.ne'
    calc
      beta = Real.artanh (Real.tanh beta) := (Real.artanh_tanh beta).symm
      _ = Real.artanh 0 := by rw [hzero]
      _ = 0 := by simp
  rw [ons_finiteTwoPoint_highTemp_ratio
    (ons_rectDualGraph M N) beta path.source_ne_target]
  push_cast
  rw [← Complex.ofReal_tanh]
  rw [div_pow,
    coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet embedding path htanh,
    coe_ons_rectDual_X_sq_eq_kwDet embedding]


theorem coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((ons_signedLoopCriticalWeight : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathDefectKWDet embedding path
          ons_signedLoopCriticalWeight) /
        ons_rectDualKWDet embedding ons_signedLoopCriticalWeight := by
  simpa [tanh_ons_betaC] using
    (coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
      embedding path ons_betaC_pos)


theorem ons_rectDualPath_critical_defectKWDet_eq_signedLoopObservable
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    ons_rectDualPathDefectKWDet embedding path ons_signedLoopCriticalWeight =
      ons_rectDualPathSignedLoopObservable path ons_signedLoopCriticalWeight :=
  ons_rectDualPath_defectKWDet_eq_signedLoopObservable embedding path
    ons_signedLoopCriticalWeight_pos.ne'

end
end StatMech.Onsager
