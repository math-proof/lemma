/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalCoverageExclusiveGoodSwap_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    Function.Injective (canonicalCoverageExclusiveGoodSwap
      ends m j k l zero hloop hjk hkl p a b hab) := by
  intro c e hce
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hraw := congrArg
    (fun x : ↥(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p b a) => x.1.1.1) hce
  change canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1.1 =
    canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 e.1.1.1 at hraw
  have hinv := congrArg
    (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1) hraw
  simpa only [canonicalQuadrangleCompletion_involutive] using hinv


theorem card_canonicalCoverageExclusiveGoodQuadrangles_comm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    #(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b) =
      #(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p b a) := by
  apply le_antisymm
  · exact Finset.card_le_card_of_injective
      (canonicalCoverageExclusiveGoodSwap_injective
        ends m j k l zero hloop hjk hkl p a b hab)
  · exact Finset.card_le_card_of_injective
      (canonicalCoverageExclusiveGoodSwap_injective
        ends m j k l zero hloop hjk hkl p b a
          (canonicalMaskTransferOrbit_symm ends m j k l zero p hab))


end StatMech.GrahamGHS.FourColor
