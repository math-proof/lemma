import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_determinant_V_l1_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {P : MvPolynomial (Fin (n + 1)) ℤ}
  {r : Fin (n + 1) → ℕ}
-- given
  (d : RothDeterminantData P r) :
-- imply
  rothMvL1 d.V ≤
    2 ^ (d.k * d.k + d.k * (∑ h : Fin n, r h.castSucc)) * rothMvL1 P ^ d.k := by
-- proof
  have succ_le_two_pow {n : ℕ} (hn : 0 < n) : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => omega
    | succ n ih =>
      if hn0 : n = 0 then
        subst n
        norm_num
      else
        calc
          _ ≤ 2 * (n + 1) := by omega
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (ih (Nat.pos_of_ne_zero hn0))
          _ = 2 ^ (n + 1) := by
            rw [pow_succ]
            ring
  have factorial_le_two_pow_sq {k : ℕ} (hk : 0 < k) :
    k.factorial ≤ 2 ^ (k * k) := by
    have hktwo : k ≤ 2 ^ k :=
      (Nat.le_add_right k 1).trans (succ_le_two_pow hk)
    calc
      _ ≤ k ^ k := Nat.factorial_le_pow k
      _ ≤ (2 ^ k) ^ k := by gcongr
      _ = 2 ^ (k * k) := by rw [pow_mul]
  calc
    _ ≤ d.k.factorial * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ d.k :=
      d.V_l1
    _ ≤ 2 ^ (d.k * d.k) * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ d.k := by
      gcongr
      exact factorial_le_two_pow_sq d.k_pos
    _ = 2 ^ (d.k * d.k + d.k * (∑ h : Fin n, r h.castSucc)) * rothMvL1 P ^ d.k := by
      rw [mul_pow, ← pow_mul]
      have hring :
        2 ^ (d.k * d.k) *
            (2 ^ ((∑ h : Fin n, r h.castSucc) * d.k) * rothMvL1 P ^ d.k) =
          (2 ^ (d.k * d.k) * 2 ^ ((∑ h : Fin n, r h.castSucc) * d.k)) *
            rothMvL1 P ^ d.k := by
        ring
      rw [hring, ← pow_add]
      congr 2
      ring


-- created on 2026-10-21
