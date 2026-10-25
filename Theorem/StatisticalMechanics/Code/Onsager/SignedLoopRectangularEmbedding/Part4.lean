/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
open Set SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem coe_ons_rectDual_X_sq_eq_canonicalKWDet
    (M N : Nat) (x : Real) :
    (ons_X (ons_rectDualGraph M N) x : Complex) ^ 2 =
      ons_rectDualCanonicalKWDet M N x :=
  coe_ons_rectDual_X_sq_eq_kwDet
    (ons_rectDualStraightLineEmbedding M N) x

theorem coe_ons_rectDualPath_sourceX_sq_eq_canonicalDefectKWDet
    {M N : Nat} (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    (ons_sourceX (ons_rectDualGraph M N)
        {path.source, path.target} x : Complex) ^ 2 =
      (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path x :=
  coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet
    (ons_rectDualStraightLineEmbedding M N) path hx

theorem ons_rectDualPath_canonicalDefectKWDet_eq_signedLoopObservable
    {M N : Nat} (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    ons_rectDualPathCanonicalDefectKWDet path x =
      ons_rectDualPathSignedLoopObservable path x :=
  ons_rectDualPath_defectKWDet_eq_signedLoopObservable
    (ons_rectDualStraightLineEmbedding M N) path hx

theorem coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
    {M N : Nat} (path : ons_RectDualPath M N)
    {beta : Real} (hbeta : 0 < beta) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((Real.tanh beta : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path (Real.tanh beta)) /
        ons_rectDualCanonicalKWDet M N (Real.tanh beta) :=
  coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
    (ons_rectDualStraightLineEmbedding M N) path hbeta

theorem coe_ons_rectDualPath_criticalTwoPoint_sq_eq_canonicalKWDet_ratio
    {M N : Nat} (path : ons_RectDualPath M N) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((ons_signedLoopCriticalWeight : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path
          ons_signedLoopCriticalWeight) /
        ons_rectDualCanonicalKWDet M N ons_signedLoopCriticalWeight :=
  coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
    (ons_rectDualStraightLineEmbedding M N) path

end
end StatMech.Onsager
