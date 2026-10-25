/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part10
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalReferenceReturnRaw_involutive
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) :
    canonicalReferenceReturnRaw ends m k zero r
        (canonicalReferenceReturnRaw ends m k zero r c) = c := by
  unfold canonicalReferenceReturnRaw
  rw [canonicalTransfer_oppositeReturn_eq_middleSwap]
  exact middleSwap_involutive m c


theorem canonicalReferenceReturnRaw_eq_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c d : ↑m -> Fin 4) :
    canonicalReferenceReturnRaw ends m k zero r c = d ↔
      canonicalReferenceReturnRaw ends m k zero r d = c := by
  constructor <;> intro h
  · rw [← h, canonicalReferenceReturnRaw_involutive]
  · rw [← h, canonicalReferenceReturnRaw_involutive]


end StatMech.GrahamGHS.FourColor
