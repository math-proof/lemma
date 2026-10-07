import sympy.matrices.block_swap
import sympy.Basic
import Lemma.Fin.GetPowFinRotate_Add_1.eq.Add
open Fin Equiv Matrix.BlockSwap


@[main]
private lemma main
-- given
  (a b : ℕ)
  (hN : 0 < a + b) :
-- imply
  tau a b = ((finCongr (show a + b - 1 + 1 = a + b by omega)).symm.trans
      ((finRotate (a + b - 1 + 1)) ^ a)).trans (finCongr (show a + b - 1 + 1 = a + b by omega)) := by
-- proof
  have e : a + b - 1 + 1 = a + b := by omega
  ext v
  simp only [tau, Equiv.trans_apply, finCongr_apply, finCongr_symm, Fin.val_cast]
  rw [GetPowFinRotate_Add_1.eq.Add, Fin.val_cast]
  obtain h | h := lt_or_ge (v : ℕ) b
  ·
    have : (finSumFinEquiv.symm (Fin.cast (Nat.add_comm a b) v) : Fin b ⊕ Fin a) = Sum.inl ⟨v, h⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp
    rw [this]; simp [e, Nat.mod_eq_of_lt (show (v : ℕ) + a < a + b by omega)]; omega
  ·
    have : (finSumFinEquiv.symm (Fin.cast (Nat.add_comm a b) v) : Fin b ⊕ Fin a) = Sum.inr ⟨v - b, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp; omega
    rw [this]; simp [e]
    rw [show (v : ℕ) + a = (v - b) + (a + b) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]


-- created on 2026-10-07
