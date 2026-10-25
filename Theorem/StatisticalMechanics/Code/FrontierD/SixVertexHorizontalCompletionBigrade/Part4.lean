/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexVerticalColumnCompletion_step_eq
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    {i : Fin T.width}
    (first second : SixVertexVerticalColumnCompletion T horizontal i)
    (j : Fin T.height)
    (hprevious : first.1
        (SixVertexArrows.cyclicPred T.height_pos j) =
      second.1 (SixVertexArrows.cyclicPred T.height_pos j)) :
    first.1 j = second.1 j := by
  have hfirst := first.2 j
  have hsecond := second.2 j
  rw [hprevious] at hfirst
  generalize hfv : first.1 j = fv at hfirst
  generalize hsv : second.1 j = sv at hsecond
  cases fv <;> cases sv <;> simp_all


theorem sixVertexVerticalColumnCompletionAtSeam_subsingleton
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width) (seam : Bool) :
    Subsingleton
      (SixVertexVerticalColumnCompletionAtSeam
        T horizontal i seam) := by
  constructor
  intro first second
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rcases T with
    ⟨width, height, widthPos, heightPos, widthEven, heightEven⟩
  obtain ⟨height, rfl⟩ := Nat.exists_eq_succ_of_ne_zero heightPos.ne'
  induction j using Fin.induction with
  | zero =>
      apply sixVertexVerticalColumnCompletion_step_eq first.1 second.1 0
      change first.1.1
          (SixVertexArrows.cyclicPred heightPos
            (0 : Fin (height + 1))) =
        second.1.1
          (SixVertexArrows.cyclicPred heightPos
            (0 : Fin (height + 1)))
      have hpred :
          SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1)) =
            svFinLast heightPos := by
        apply Fin.ext
        simp [SixVertexArrows.cyclicPred, svFinLast]
      rw [hpred, first.2, second.2]
  | succ j ih =>
      apply sixVertexVerticalColumnCompletion_step_eq
        first.1 second.1 j.succ
      simpa [svCyclicPred_succ] using ih


end
end StatMech.FrontierD
