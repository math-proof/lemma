/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOpenAdjacencyEvent_isIncreasing
    (R : FKRectTorus) (x y : R.Vertex) :
    IsIncreasing (fkRectOpenAdjacencyEvent R x y) := by
  intro omega tau hot hadj
  exact fkRectOpenGraph_mono R hot hadj


theorem fkRectVerticalCutGraph_mono (R : FKRectTorus)
    {omega tau : R.Configuration} (hot : omega ≤ tau) :
    fkRectVerticalCutGraph R omega ≤ fkRectVerticalCutGraph R tau := by
  intro x y hxy
  unfold fkRectVerticalCutGraph at hxy ⊢
  rw [SimpleGraph.deleteEdges_adj] at hxy ⊢
  exact ⟨fkRectOpenGraph_mono R hot hxy.1, hxy.2⟩

theorem fkRectVerticalCutGraph_le_openGraph (R : FKRectTorus)
    (omega : R.Configuration) :
    fkRectVerticalCutGraph R omega ≤ fkRectOpenGraph R omega := by
  intro x y hxy
  unfold fkRectVerticalCutGraph at hxy
  exact (SimpleGraph.deleteEdges_adj.mp hxy).1


theorem fkRectVerticalSeamIncrement_eq_zero_of_not_crosses
    (R : FKRectTorus) (x y : R.Vertex)
    (hnot : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectVerticalSeamIncrement R x y = 0 := by
  unfold fkRectVerticalSeamIncrement
  by_cases hpos : x.2.val + 1 = R.height ∧ y.2.val = 0
  · exact False.elim (hnot (Or.inr ⟨hpos.2, hpos.1⟩))
  by_cases hneg : x.2.val = 0 ∧ y.2.val + 1 = R.height
  · exact False.elim (hnot (Or.inl hneg))
  simp [hpos, hneg]


theorem fkRectVerticalSeamIncrement_ne_zero_of_crosses
    (R : FKRectTorus) (x y : R.Vertex)
    (hcross : fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectVerticalSeamIncrement R x y ≠ 0 := by
  have hheight : R.height ≠ 1 :=
    Nat.ne_of_gt (lt_trans Nat.one_lt_two R.height_gt_two)
  rcases hcross with hcross | hcross
  · change x.2.val = 0 ∧ y.2.val + 1 = R.height at hcross
    have hfirst : ¬ (x.2.val + 1 = R.height ∧ y.2.val = 0) := by
      intro h
      omega
    unfold fkRectVerticalSeamIncrement
    rw [if_neg hfirst, if_pos hcross]
    norm_num
  · change y.2.val = 0 ∧ x.2.val + 1 = R.height at hcross
    have hfirst : x.2.val + 1 = R.height ∧ y.2.val = 0 :=
      ⟨hcross.2, hcross.1⟩
    unfold fkRectVerticalSeamIncrement
    rw [if_pos hfirst]
    norm_num


theorem fkRectVerticalCutWalk_winding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (p : (fkRectVerticalCutGraph R omega).Walk x y) :
    (fkRectWalkWinding R p).2 = 0 := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      have hnot : ¬ fkRectCrossesVerticalSeam R s(u, v) := by
        unfold fkRectVerticalCutGraph at huv
        exact (SimpleGraph.deleteEdges_adj.mp huv).2
      simp only [fkRectWalkWinding]
      rw [fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R u v hnot,
        ih, zero_add]


theorem FKRectVerticalWindingWitness.exists_closedWalk_winding_snd_ne_zero
    (R : FKRectTorus) (omega : R.Configuration) (x y : R.Vertex)
    (h : FKRectVerticalWindingWitness R omega x y) :
    ∃ p : (fkRectOpenGraph R omega).Walk x x,
      (fkRectWalkWinding R p).2 ≠ 0 := by
  obtain ⟨p⟩ := h.2.2
  let p' := p.mapLe (fkRectVerticalCutGraph_le_openGraph R omega)
  let c := p'.concat h.1.symm
  refine ⟨c, ?_⟩
  have hpzero := fkRectVerticalCutWalk_winding_snd_eq_zero R omega p
  have hseamSwap : fkRectCrossesVerticalSeam R s(y, x) := by
    simpa only [Sym2.eq_swap] using h.2.1
  have hstep := fkRectVerticalSeamIncrement_ne_zero_of_crosses
    R y x hseamSwap
  rw [show c = p'.concat h.1.symm from rfl,
    SimpleGraph.Walk.concat_eq_append, fkRectWalkWinding_append,
    show fkRectWalkWinding R p' = fkRectWalkWinding R p from
      fkRectWalkWinding_mapLe R
        (fkRectVerticalCutGraph_le_openGraph R omega) p]
  simp only [fkRectWalkWinding]
  rw [hpzero, zero_add, add_zero]
  exact hstep


end
end StatMech.FrontierD
