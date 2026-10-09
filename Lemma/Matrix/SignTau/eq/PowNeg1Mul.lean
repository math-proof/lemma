import sympy.matrices.block_swap
import sympy.Basic
import Lemma.Matrix.Tau.eq.TransFinCongrPowFinRotate.of.Gt_0
open Matrix Equiv Matrix.BlockSwap


@[path]
private lemma main
-- given
  (a b : ℕ) :
-- imply
  Perm.sign (tau a b) = (-1) ^ (a * b) := by
-- proof
  obtain h0 | hN := Nat.eq_zero_or_pos (a + b)
  ·
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have : tau 0 0 = 1 := Equiv.ext (fun v => v.elim0)
    rw [this, map_one]
    rfl
  ·
    rw [Tau.eq.TransFinCongrPowFinRotate.of.Gt_0 a b hN, Perm.sign_symm_trans_trans, map_pow, sign_finRotate, ← pow_mul]
    have key : ∀ t : ℕ, t + 1 = a + b → (-1 : ℤˣ) ^ (t * a) = (-1) ^ (a * b) := by
      intro t ht
      obtain _ | a := a
      · simp
      ·
        have h3 : t * (a + 1) = a * (a + 1) + (a + 1) * b := by
          obtain rfl : t = a + b := by omega
          ring
        rw [h3, pow_add, (Nat.even_mul_succ_self a).neg_one_pow, one_mul]
    exact key _ (by omega)


-- created on 2026-10-07
