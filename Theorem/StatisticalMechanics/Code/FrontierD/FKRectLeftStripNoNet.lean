/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectTorusGraph_adj_crosses_column_cut
    (R : FKRectTorus) (right : Nat) (hright : right + 1 < R.width)
    {u v : R.Vertex} (hu : u.1.val ≤ right) (hv : right < v.1.val)
    (hadj : (fkRectTorusGraph R).Adj u v)
    (hnot : ¬ fkRectCrossesHorizontalSeam R s(u, v)) :
    u.1.val = right ∧ v.1.val = right + 1 := by
  rcases hadj with ⟨⟨b, x, y⟩, hedge⟩
  cases b
  · by_cases hy : Even y.val
    · simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · have hu' := congrArg (fun z => z.1.val) h.1
        have hv' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hv'
        split at hv'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          left
          have hwidth := R.width_pos
          constructor
          · omega
          · omega
        · omega
      · have hv' := congrArg (fun z => z.1.val) h.1
        have hu' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hu'
        split at hu'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          right
          have hwidth := R.width_pos
          constructor <;> omega
        · omega
    · simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_false] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · have hu' := congrArg (fun z => z.1.val) h.1
        have hv' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hu'
        split at hu'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          right
          have hwidth := R.width_pos
          constructor <;> omega
        · omega
      · have hv' := congrArg (fun z => z.1.val) h.1
        have hu' := congrArg (fun z => z.1.val) h.2
        simp only [Prod.fst] at hu' hv'
        rw [fkRectCyclicPred_val] at hv'
        split at hv'
        · exfalso
          apply hnot
          rw [fkRectCrossesHorizontalSeam_mk]
          left
          have hwidth := R.width_pos
          constructor <;> omega
        · omega
  · simp only [fkRectTorusIndexedEdge, if_true] at hedge
    rcases Sym2.eq_iff.mp hedge with h | h
    · have huv := congrArg (fun z => z.1.val) h.1
      have hvu := congrArg (fun z => z.1.val) h.2
      simp only [Prod.fst] at huv hvu
      omega
    · have huv := congrArg (fun z => z.1.val) h.1
      have hvu := congrArg (fun z => z.1.val) h.2
      simp only [Prod.fst] at huv hvu
      omega


end
end StatMech.FrontierD
