/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge.Part4


namespace StatMech.FrontierA

open StatMech.Onsager


theorem triangularTorusSpinDartGauge_ne_zero
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) :
    triangularTorusSpinDartGauge L a b d ≠ 0 :=
  inv_ne_zero (triangularTorusSpinVertexGauge_ne_zero L a b d.1)


theorem triangularTorusKWMatrix_spin_eq_diagonalGauge_seam
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    triangularTorusKWMatrix L t1 t2 t3 rho
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_diagonalGaugeMatrix (triangularTorusSpinDartGauge L a b)
        (triangularTorusSeamKWMatrix L t1 t2 t3 rho a b) := by
  ext d e
  unfold triangularTorusKWMatrix ons_blockCirculant2D
    triangularTorusKWBlock triangularTorusSeamKWMatrix
    ons_diagonalGaugeMatrix triangularTorusSpinDartGauge
  by_cases hstep : (d.1.1 - e.1.1, d.1.2 - e.1.2) =
      triangularTorusDirectionStep L d.2
  · rw [if_pos hstep]
    simp only [triangularTorusSeamKWMatrix, if_pos hstep]
    have hepos : e.1 = d.1 - triangularTorusDirectionStep L d.2 := by
      rw [← hstep]
      apply Prod.ext <;> simp
    have hg := triangularTorusDirectionPhase_mul_vertexGauge L a b d
    rw [← hepos] at hg
    have hdg := triangularTorusSpinVertexGauge_ne_zero L a b d.1
    have heg := triangularTorusSpinVertexGauge_ne_zero L a b e.1
    field_simp [hdg, heg]
    linear_combination hg *
      (triangularTorusDirectionWeight t1 t2 t3 d.2 *
        triangularKacWardTurnMatrix rho d.2 e.2)
  · rw [if_neg hstep]
    simp only [triangularTorusSeamKWMatrix, if_neg hstep]
    ring


theorem det_ons_diagonalGaugeMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    (gauge : E -> Complex) (hgauge : forall e, gauge e ≠ 0)
    (M : Matrix E E Complex) :
    (ons_diagonalGaugeMatrix gauge M).det = M.det := by
  classical
  let N : Matrix E E Complex := fun i j => gauge i * M i j
  have hleft : Matrix.diagonal gauge * M = N := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, N]
  have hright : N * Matrix.diagonal (fun e => (gauge e)⁻¹) =
        ons_diagonalGaugeMatrix gauge M := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, N,
      ons_diagonalGaugeMatrix]
  have hmatrix : ons_diagonalGaugeMatrix gauge M =
      Matrix.diagonal gauge * M *
        Matrix.diagonal (fun e => (gauge e)⁻¹) := by
    rw [hleft, hright]
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_inv_distrib]
  have hprod : (∏ e, gauge e) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun e _ => hgauge e)
  field_simp [hprod]


theorem det_one_sub_triangularTorusKWMatrix_spin_eq_seam
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    (1 - triangularTorusKWMatrix L t1 t2 t3 rho
        (ons_spinPhase L a) (ons_spinPhase L b)).det =
      (1 - triangularTorusSeamKWMatrix L t1 t2 t3 rho a b).det := by
  rw [triangularTorusKWMatrix_spin_eq_diagonalGauge_seam]
  let gauge := triangularTorusSpinDartGauge L a b
  let M := triangularTorusSeamKWMatrix L t1 t2 t3 rho a b
  have hsub : 1 - ons_diagonalGaugeMatrix gauge M =
      ons_diagonalGaugeMatrix gauge (1 - M) := by
    ext d e
    by_cases hde : d = e
    · subst e
      have hg : gauge d ≠ 0 :=
        triangularTorusSpinDartGauge_ne_zero L a b d
      simp only [Matrix.sub_apply, Matrix.one_apply, if_pos,
        ons_diagonalGaugeMatrix]
      field_simp [hg]
    · simp [ons_diagonalGaugeMatrix, Matrix.one_apply, hde]
  rw [hsub, det_ons_diagonalGaugeMatrix gauge
    (triangularTorusSpinDartGauge_ne_zero L a b)]

end StatMech.FrontierA
