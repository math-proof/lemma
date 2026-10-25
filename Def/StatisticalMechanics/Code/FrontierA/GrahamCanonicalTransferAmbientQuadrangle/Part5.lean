/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


set_option maxHeartbeats 1000000 in


noncomputable def canonicalCoverageExclusiveGoodSwap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    ↥(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b) ->
      ↥(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p b a) := fun c => by
  have hc := (mem_canonicalCoverageExclusiveGoodQuadrangles_iff
    ends m j k l zero p a b c.1).mp c.2
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c.1 hc.2.2
  have hdExclusive := quadrangleCompletion_mem_coverage_sdiff
    hloop hjk hkl a b c.1 hab hc.1 hc.2.1 hc.2.2
  refine ⟨d, (mem_canonicalCoverageExclusiveGoodQuadrangles_iff
    ends m j k l zero p b a d).mpr ⟨hdExclusive.1, hdExclusive.2, ?_⟩⟩
  change RowsDisconnect ends m
    (canonicalQuadrangleCompletion ends m k zero b.1.1 a.1.1 d.1.1) k zero
  rw [show d.1.1 = canonicalQuadrangleCompletion ends m k zero
    a.1.1 b.1.1 c.1.1.1 from rfl]
  rw [canonicalQuadrangleCompletion_comm ends m k zero b.1.1 a.1.1]
  rw [canonicalQuadrangleCompletion_involutive]
  exact c.1.1.2.2.2.2.2

end StatMech.GrahamGHS.FourColor
