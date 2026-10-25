/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBondLabel


namespace StatMech.FrontierD

theorem fkRectTorusMedialEdgeEquiv_bondMate
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectTorusMedialEdgeEquiv R (fkMedialBondMate R.medialTorus d).1 =
      fkRectMedialBondEdgeIndex R
        (fkRectTorusMedialEdgeEquiv R d.1) d.2 := by
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e := by
    exact ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases b <;> cases side
  all_goals
    apply (fkRectTorusMedialEdgeEquiv R).symm.injective
    simp only [Equiv.symm_apply_apply]
    simp only [fkRectTorusMedialEdgeEquiv_vertexOfEdge]
    apply Prod.ext
    · apply Fin.ext
      rw [fkRectTorusMedialEdgeEquiv_symm_fst_val]
      simp [fkMedialBondMate, fkRectMedialBondEdgeIndex,
        fkRectMedialVertexOfEdge_fst_val,
        fkRectTorusMedialEdgeEquiv_vertexOfEdge, Fin.val_mk,
        Bool.toNat, FKRectTorus.medialTorus, finitePeriodicSucc,
        SixVertexArrows.cyclicPred] <;>
      first
      | (omega; done)
      | simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          double_cyclicPred R.width x.val R.width_pos x.isLt
      | simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          double_finitePeriodicSucc R.width x.val R.width_pos x.isLt
      | (rw [show 1 + 2 * x.val + 2 * R.width - 1 =
            2 * x.val + 2 * R.width by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; done)
      | (rw [Nat.mod_eq_of_lt (by omega)]; done)
      | exact Nat.mod_eq_of_lt (double_add_one_lt R.width x.val x.isLt)
      | exact Nat.mod_eq_of_lt (double_mul_add_one_lt R.width x.val x.isLt)
      | exact double_mul_add_one_mod R.width x.val x.isLt
      | ac_rfl
    · rw [fkRectTorusMedialEdgeEquiv_symm_snd] <;>
      (simp [fkMedialBondMate, fkRectMedialBondEdgeIndex,
        fkRectMedialVertexOfEdge_snd] <;> rfl)


theorem fkRectMedialDartPrimalLabel_bondMate
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R (fkMedialBondMate R.medialTorus d) =
      fkRectMedialDartPrimalLabel R d := by
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hi := fkRectTorusMedialEdgeEquiv_bondMate R (v, side)
  change fkRectTorusMedialEdgeEquiv R
      (fkMedialBondMate R.medialTorus (v, side)).1 =
    fkRectMedialBondEdgeIndex R e side at hi
  cases side <;>
    simp only [fkMedialBondMate] at hi ⊢ <;>
    unfold fkRectMedialDartPrimalLabel <;>
    rw [hi, show fkRectTorusMedialEdgeEquiv R v = e from rfl] <;>
    rcases e with ⟨b, x, y⟩ <;> cases b <;>
    by_cases hy : Even y.val <;>
    simp [fkRectMedialBondEdgeIndex, fkRectMedialWestPrimal,
      fkRectMedialEastPrimal, fkRectClosedPairingAtEdge, hy,
      even_finitePeriodicSucc_iff, even_cyclicPred_iff,
      finitePeriodicSucc_cyclicPred, svCyclicPred_finitePeriodicSucc]

end StatMech.FrontierD
