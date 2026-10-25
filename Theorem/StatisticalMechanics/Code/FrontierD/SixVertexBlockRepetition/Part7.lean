/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part6
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleStraightExtend_boundary
    {N M r q : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (z : Fin r → Bool)
    (ω : SixVertexRectangleBoundaryFiber
      (sixVertexToroidalRectangleBoundary ξ)) :
    sixVertexRectangleBoundary (sixVertexRectangleStraightExtend z ω.1) =
      sixVertexToroidalRectangleBoundary
        (sixVertexStraightExtendedToroidalBoundary q ξ z) := by
  apply SixVertexRectangleBoundary.ext
  · funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have h := congrArg (fun η => η.left k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]
  · funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have h := congrArg (fun η => η.right k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      have h := congrArg (fun η => η.bottom k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      have h := congrArg (fun η => η.top k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]


end StatMech.FrontierD
