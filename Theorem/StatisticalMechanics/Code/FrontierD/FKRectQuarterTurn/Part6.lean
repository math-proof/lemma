/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part6
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectQuarterTurnEdgeEquiv_apply
    (R : FKRectTorus) (hheight : 4 < R.height) (a : R.EdgeIndex) :
    fkRectQuarterTurnEdgeEquiv R hheight a =
      fkRectQuarterTurnEdge R hheight a := rfl


theorem fkRectTorusIndexedEdge_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnEdgeEquiv R hheight a) =
      Sym2.map (fkRectQuarterTurnVertexEquiv R hheight)
        (fkRectTorusIndexedEdge R a) := by
  have hH := fkRectHeight_two_mul_div_two R
  have hW := R.width_gt_two
  rcases a with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val
  · obtain ⟨k, hk⟩ := hy
    have hyeven : Even y.val := ⟨k, hk⟩
    have hymod : y.val % 2 = 0 := by omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, Nat.reduceEqDiff, decide_false,
      Bool.false_eq_true, if_false, even_two_mul, if_true,
      fkRectTorusIndexedEdge, fkRectQuarterTurnVertexEquiv_apply,
      fkRectQuarterTurnVertex, Bool.toNat_false, Nat.add_zero, hyeven,
      Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega
  · have hymodlt := Nat.mod_lt y.val (by norm_num : 0 < 2)
    have hymod : y.val % 2 = 1 := by
      by_contra h
      apply hy
      rw [Nat.even_iff]
      omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, decide_true, if_true,
      fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy,
      fkRectQuarterTurnVertexEquiv_apply, fkRectQuarterTurnVertex,
      Bool.toNat_false, Nat.add_zero, even_two_mul, Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega
  · obtain ⟨k, hk⟩ := hy
    have hyeven : Even y.val := ⟨k, hk⟩
    have hymod : y.val % 2 = 0 := by omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, Nat.reduceEqDiff, decide_false,
      Bool.true_eq_false, if_true, Nat.reduceAdd, Nat.not_even_one,
      if_false, fkRectTorusIndexedEdge, fkRectQuarterTurnVertexEquiv_apply,
      fkRectQuarterTurnVertex, Bool.toNat_true, hyeven, even_two_mul,
      Nat.even_add_one, Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega
  · have hymodlt := Nat.mod_lt y.val (by norm_num : 0 < 2)
    have hymod : y.val % 2 = 1 := by
      by_contra h
      apply hy
      rw [Nat.even_iff]
      omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, decide_true, if_true,
      fkRectTorusIndexedEdge, Nat.reduceAdd, Nat.not_even_one,
      if_false, fkRectQuarterTurnVertexEquiv_apply,
      fkRectQuarterTurnVertex, Bool.toNat_true, hy, even_two_mul,
      Nat.even_add_one, Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega


theorem fkRectTorusGraph_adj_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (x y : R.Vertex) :
    (fkRectTorusGraph (fkRectQuarterTurnTorus R hheight)).Adj
        (fkRectQuarterTurnVertexEquiv R hheight x)
        (fkRectQuarterTurnVertexEquiv R hheight y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectQuarterTurnEdgeEquiv R hheight).symm a
    refine ⟨b, ?_⟩
    have hturn := fkRectTorusIndexedEdge_quarterTurn R hheight b
    rw [(fkRectQuarterTurnEdgeEquiv R hheight).apply_symm_apply a,
      ha] at hturn
    apply Sym2.map.injective
      (fkRectQuarterTurnVertexEquiv R hheight).injective
    simpa only [Sym2.map_mk] using hturn.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectQuarterTurnEdgeEquiv R hheight a, ?_⟩
    rw [fkRectTorusIndexedEdge_quarterTurn, ha, Sym2.map_mk]


end
end StatMech.FrontierD
