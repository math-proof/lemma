import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOfVecCons_FunPow.eq.MulPowSub1Prod
open Matrix Nat


@[main]
private lemma main
  {n : ℕ}
  {r : ℝ} :
-- imply
  (Matrix.of fun (a j : Fin n) => if (a : ℕ) = 0 then 1 - r ^ ((j : ℕ) + 1) else ((j : ℝ) + 1) ^ (a : ℕ)).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
-- proof
  cases n with
  | zero => simp
  | succ k =>
    set V := Matrix.of fun (a j : Fin (k + 1)) => ((j : ℝ) + 1) ^ (a : ℕ) with hV
    set w : Fin (k + 1) → ℝ := fun j => r ^ ((j : ℕ) + 1) with hw
    have hM : (Matrix.of fun (a j : Fin (k + 1)) => if (a : ℕ) = 0 then 1 - r ^ ((j : ℕ) + 1) else ((j : ℝ) + 1) ^ (a : ℕ)) =
        V.updateRow 0 (V 0 + (-1 : ℝ) • w) := by
      ext a j
      refine Fin.cases ?_ (fun a => ?_) a
      ·
        simp [hV, hw]
        ring
      · simp [hV, hw]
    rw [hM, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
    have hN := DetOfVecCons_FunPow.eq.MulPowSub1Prod (n := k + 1) (r := r)
    set N := Matrix.of (Matrix.vecCons (fun j : Fin (k + 1 + 1) => r ^ (j : ℕ))
      (fun (i : Fin (k + 1)) (j : Fin (k + 1 + 1)) => (j : ℝ) ^ (i : ℕ))) with hNdef
    have e0 : N.submatrix (Fin.succAbove 0) Fin.succ = V := by
      ext a j
      simp [hNdef, hV]
    have e1 : N.submatrix (Fin.succAbove (Fin.succ 0)) Fin.succ = V.updateRow 0 w := by
      ext a j
      refine Fin.cases ?_ (fun a => ?_) a
      · simp [hNdef, hV, hw]
      · simp [hNdef, hV, hw]
    have hrest : ∑ i : Fin k, (-1 : ℝ) ^ ((Fin.succ (Fin.succ i) : Fin (k + 1 + 1)) : ℕ) * N (Fin.succ (Fin.succ i)) 0 *
        (N.submatrix (Fin.succAbove (Fin.succ (Fin.succ i))) Fin.succ).det = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hNdef]
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, hrest, e0, e1] at hN
    rw [← hN]
    simp [hNdef]


-- created on 2026-10-07
