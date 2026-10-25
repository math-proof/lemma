/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialVertexParity_cyclicNeg
    {T : EvenTorus} (v : T.Vertex) :
    fkMedialVertexParity (sixVertexCyclicNeg T.width_pos v.1, v.2) =
      fkMedialVertexParity v := by
  unfold fkMedialVertexParity
  have hEven := sixVertexCyclicNeg_even_iff
    T.width_pos T.width_even v.1
  have hdecide : decide (Even (sixVertexCyclicNeg T.width_pos v.1).val) =
      decide (Even v.1.val) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hEven
  rw [hdecide]

theorem sixVertexHorizontalGaugeBit_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (v : T.Vertex) :
    sixVertexHorizontalGaugeBit
        (sixVertexReflectHorizontalField horizontal) v =
      sixVertexHorizontalGaugeBit horizontal
        (sixVertexCyclicNeg T.width_pos v.1, v.2) := by
  unfold sixVertexHorizontalGaugeBit sixVertexReflectHorizontalField
  rw [fkMedialVertexParity_cyclicNeg]

theorem sixVertexHorizontalZeroCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalZeroCount
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexHorizontalZeroCount horizontal := by
  let vertexEquiv : T.Vertex ≃ T.Vertex :=
    { toFun := fun v => (sixVertexCyclicNeg T.width_pos v.1, v.2)
      invFun := fun v => (sixVertexCyclicNeg T.width_pos v.1, v.2)
      left_inv := fun v => by
        apply Prod.ext
        · exact sixVertexCyclicNeg_involutive T.width_pos v.1
        · rfl
      right_inv := fun v => by
        apply Prod.ext
        · exact sixVertexCyclicNeg_involutive T.width_pos v.1
        · rfl }
  unfold sixVertexHorizontalZeroCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv vertexEquiv
  intro v
  change sixVertexHorizontalGaugeBit
      (sixVertexReflectHorizontalField horizontal) v = false ↔
    sixVertexHorizontalGaugeBit horizontal (vertexEquiv v) = false
  rw [sixVertexHorizontalGaugeBit_reflect]
  rfl

theorem sixVertexHorizontalNontransitionCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalNontransitionCount
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexHorizontalNontransitionCount horizontal := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  let vertexEquiv : T.Vertex ≃ T.Vertex :=
    xEquiv.prodCongr (Equiv.refl _)
  unfold sixVertexHorizontalNontransitionCount
  calc
    (∑ v : T.Vertex,
      if sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal)
            (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
          sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal) v
      then 1 else 0) =
        ∑ v : T.Vertex,
          if sixVertexHorizontalGaugeBit horizontal
                (SixVertexArrows.cyclicPred T.width_pos
                  (vertexEquiv v).1, (vertexEquiv v).2) =
              sixVertexHorizontalGaugeBit horizontal (vertexEquiv v)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [sixVertexHorizontalGaugeBit_reflect,
        sixVertexHorizontalGaugeBit_reflect]
      have hnegPred := sixVertexCyclicNeg_cyclicPred
        T.width_pos v.1
      have hpredSucc := svCyclicPred_finitePeriodicSucc
        T.width_pos (sixVertexCyclicNeg T.width_pos v.1)
      change (if sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos
              (SixVertexArrows.cyclicPred T.width_pos v.1), v.2) =
          sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos v.1, v.2)
        then 1 else 0) = _
      rw [hnegPred]
      have hvertex : vertexEquiv v =
          (finitePeriodicSucc T.width_pos
            (sixVertexCyclicNeg T.width_pos v.1), v.2) := by
        rfl
      rw [hvertex, hpredSucc]
      simp only [eq_comm]
    _ = _ := by
      exact vertexEquiv.sum_comp fun v =>
        if sixVertexHorizontalGaugeBit horizontal
              (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
            sixVertexHorizontalGaugeBit horizontal v
        then 1 else 0

end
end StatMech.FrontierD
