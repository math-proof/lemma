/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem norm_ons_rectDualEdgeSignDefect
    (M N : Nat)
    (defect : Sym2 (ons_RectDualVertex M N) → Prop)
    [DecidablePred defect] {q : Real} (hq : 0 ≤ q)
    (edge : Sym2 (ons_RectDualVertex M N)) :
    ‖ons_rectDualEdgeSignDefect M N defect q edge‖ = q := by
  unfold ons_rectDualEdgeSignDefect
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hq]


theorem ons_rectDualSignDefect_det_ratio_eq_walk_exp
    (M N : Nat)
    (defect : Sym2 (ons_RectDualVertex M N) → Prop)
    [DecidablePred defect]
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight) :
    (1 - kwGraphTransition (ons_rectDualGraph M N)
        (ons_rectDualEdgeSignDefect M N defect q)
        (ons_rectDualStraightLineEmbedding M N).turnPhase).det /
      (1 - kwGraphTransition (ons_rectDualGraph M N)
        (fun _ ↦ (q : Complex))
        (ons_rectDualStraightLineEmbedding M N).turnPhase).det =
      Complex.exp (-(ons_rectDualWalkExponent M N
          (ons_rectDualEdgeSignDefect M N defect q) -
        ons_rectDualWalkExponent M N (fun _ ↦ (q : Complex)))) := by
  have hdef := kwGraphTransition_canonical_det_eq_walk_exp M N
    (ons_rectDualEdgeSignDefect M N defect q) q hq0 hq
    (fun edge ↦ (norm_ons_rectDualEdgeSignDefect
      M N defect hq0 edge).le)
  have hplain := kwGraphTransition_canonical_det_eq_walk_exp M N
    (fun _ ↦ (q : Complex)) q hq0 hq (fun _ ↦ by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0])
  rw [hdef, hplain, ← Complex.exp_sub]
  congr 1
  unfold ons_rectDualWalkExponent
  ring

end
end StatMech.Onsager
