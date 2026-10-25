/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut
open Finset


namespace StatMech.FrontierD

noncomputable def sixVertexTorusCutEquiv (T : EvenTorus) :
    SixVertexArrows T ≃ SixVertexCutRectangles T where
  toFun ω := ⟨sixVertexTorusSeam T ω,
    ⟨sixVertexCutTorusArrows T ω, sixVertexCutTorusArrows_boundary T ω⟩⟩
  invFun ξω := sixVertexGlueTorusArrows T ξω.2.1
  left_inv := sixVertexGlue_cut_torus_arrows T
  right_inv ξω := by
    rcases ξω with ⟨ξ, ⟨ω, hω⟩⟩
    change (⟨sixVertexTorusSeam T (sixVertexGlueTorusArrows T ω),
        ⟨sixVertexCutTorusArrows T (sixVertexGlueTorusArrows T ω),
          sixVertexCutTorusArrows_boundary T (sixVertexGlueTorusArrows T ω)⟩⟩ :
        SixVertexCutRectangles T) = ⟨ξ, ⟨ω, hω⟩⟩
    have hξ : sixVertexTorusSeam T (sixVertexGlueTorusArrows T ω) = ξ := by
      apply Prod.ext
      · funext j
        have h := congrArg (fun b => b.right j) hω
        simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
          sixVertexTorusSeam, sixVertexGlueTorusArrows] using h
      · funext i
        have h := congrArg (fun b => b.top i) hω
        simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
          sixVertexTorusSeam, sixVertexGlueTorusArrows] using h
    apply Sigma.ext hξ
    apply (Subtype.heq_iff_coe_eq (fun η => by
      change sixVertexRectangleBoundary η =
          sixVertexToroidalRectangleBoundary
            (sixVertexTorusSeam T (sixVertexGlueTorusArrows T ω)) ↔
        sixVertexRectangleBoundary η = sixVertexToroidalRectangleBoundary ξ
      rw [hξ])).2
    apply SixVertexRectangleArrows.ext
    · funext kj
      rcases kj with ⟨k, j⟩
      refine Fin.cases ?_ (fun i => ?_) k
      · have hl := congrArg (fun b => b.left j) hω
        have hr := congrArg (fun b => b.right j) hω
        have hlr : ω.horizontal (0, j) =
            ω.horizontal (Fin.last T.width, j) := by
          simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
            hl.trans hr.symm
        simpa [sixVertexCutTorusArrows, sixVertexGlueTorusArrows] using hlr.symm
      · simp [sixVertexCutTorusArrows, sixVertexGlueTorusArrows]
    · funext ik
      rcases ik with ⟨i, k⟩
      refine Fin.cases ?_ (fun j => ?_) k
      · have hb := congrArg (fun b => b.bottom i) hω
        have ht := congrArg (fun b => b.top i) hω
        have hbt : ω.vertical (i, 0) =
            ω.vertical (i, Fin.last T.height) := by
          simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
            hb.trans ht.symm
        simpa [sixVertexCutTorusArrows, sixVertexGlueTorusArrows] using hbt.symm
      · simp [sixVertexCutTorusArrows, sixVertexGlueTorusArrows]

end StatMech.FrontierD
