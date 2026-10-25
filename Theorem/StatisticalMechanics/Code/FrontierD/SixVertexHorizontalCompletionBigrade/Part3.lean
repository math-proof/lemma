/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexVerticalCompletion_step_eq
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    {first second : T.Vertex -> Bool}
    (hfirst : (sixVertexArrowsOfFields horizontal first).IceRule)
    (hsecond : (sixVertexArrowsOfFields horizontal second).IceRule)
    (i : Fin T.width) (j : Fin T.height)
    (hprevious : first
        (i, SixVertexArrows.cyclicPred T.height_pos j) =
      second (i, SixVertexArrows.cyclicPred T.height_pos j)) :
    first (i, j) = second (i, j) := by
  have hfirstVertex := hfirst (i, j)
  have hsecondVertex := hsecond (i, j)
  unfold SixVertexArrows.incomingCount sixVertexArrowsOfFields at hfirstVertex hsecondVertex
  simp only at hfirstVertex hsecondVertex
  rw [hprevious] at hfirstVertex
  generalize hfv : first (i, j) = fv at hfirstVertex
  generalize hsv : second (i, j) = sv at hsecondVertex
  cases fv <;> cases sv <;> simp_all


theorem sixVertexVerticalCompletionSeamRow_injective
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T} :
    Function.Injective
      (sixVertexVerticalCompletionSeamRow
        (T := T) (horizontal := horizontal)) := by
  rcases T with ⟨width, height, widthPos, heightPos, widthEven, heightEven⟩
  obtain ⟨height, rfl⟩ := Nat.exists_eq_succ_of_ne_zero heightPos.ne'
  intro first second hseam
  apply Subtype.ext
  funext vertex
  rcases vertex with ⟨i, j⟩
  induction j using Fin.induction with
  | zero =>
      apply sixVertexVerticalCompletion_step_eq
        first.2 second.2 i 0
      have hrow := congrFun hseam i
      change first.1 (i, svFinLast heightPos) =
        second.1 (i, svFinLast heightPos) at hrow
      change first.1
          (i, SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1))) =
        second.1
          (i, SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1)))
      have hpred :
          SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1)) =
            svFinLast heightPos := by
        apply Fin.ext
        simp [SixVertexArrows.cyclicPred, svFinLast]
      rw [hpred]
      exact hrow
  | succ j ih =>
      apply sixVertexVerticalCompletion_step_eq
        first.2 second.2 i j.succ
      simpa [svCyclicPred_succ] using ih


end
end StatMech.FrontierD
