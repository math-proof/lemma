import Lemma.Matrix.DetInterleave.eq.MulPowNeg1Sub_Det
import Lemma.Nat.Delta.eq.Ite
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open Matrix Nat Fin


@[path]
private lemma main :
-- imply
  (interleave d).det = (-1 : ℝ) ^ (d / 2) := by
-- proof
  induction d with
  | zero =>
    rw [Matrix.det_fin_zero]
    norm_num
  | succ d ih =>
    cases d with
    | zero =>
      have hP : interleave 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [interleave, Delta.eq.Ite]
      rw [hP, Matrix.det_one]
      norm_num
    | succ n =>
      have hd : 1 < n + 2 := by omega
      have hrec := DetInterleave.eq.MulPowNeg1Sub_Det (hd := hd)
      have hdim : n + 2 - 1 = n + 1 := Nat.add_sub_cancel (n + 1) 1
      simp [hdim] at hrec
      rw [hrec, ih]
      obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd (n + 2)
      ·
        have hn : n + 1 = 2 * k - 1 := by omega
        have hgoal : (n + 2) / 2 = k := by omega
        have hdiv : (2 * k - 1) / 2 = k - 1 := by omega
        rw [hgoal, hn, hdiv]
        have hodd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
        rw [Odd.neg_one_pow hodd]
        obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd k
        ·
          have hkm : Odd (k - 1) := ⟨m - 1, by omega⟩
          rw [Odd.neg_one_pow hkm, Even.neg_one_pow ⟨m, hm⟩]
          norm_num
        ·
          have hkm : Even (k - 1) := ⟨m, by omega⟩
          rw [Even.neg_one_pow hkm, Odd.neg_one_pow ⟨m, hm⟩]
          norm_num
      ·
        have hn : n + 1 = 2 * k := by omega
        have hgoal : (n + 2) / 2 = k := by omega
        have hdiv : 2 * k / 2 = k := by omega
        rw [hgoal, hn, hdiv, Even.neg_one_pow (even_two_mul k)]
        ring


-- created on 2026-11-01
