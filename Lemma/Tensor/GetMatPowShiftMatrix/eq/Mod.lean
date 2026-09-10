import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetShiftMatrix.eq.ModAddOne
import Lemma.Tensor.MatProd.eq.DotMatProd
import Lemma.Tensor.Mul
import sympy.matrices.expressions.matpow
open Nat Tensor


@[main, fin]
private lemma main
  [CommRing α] [CharZero α]
  (n : ℕ) (h : 0 < n)
  (k : ℕ)
  (i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) n 0 (n - 1) ^ (k : ℤ))[i, j] =
    (↑(KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ)) : Tensor α []) := by
-- proof
  induction k generalizing j with
  | zero =>
    show (Tensor.eye (α := α) n)[i, j] = _
    have heye := GetEye.eq.Delta.fin (α := α) i j
    simp only [GetElem.getElem] at heye ⊢
    apply heye.trans
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega : (i : ℕ) < n)]
    simp [Delta.eq.Ite, Fin.val_inj]
    rfl
  | succ k ih =>
    have hpow : (ShiftMatrix (α := α) n 0 (n - 1) ^ (((k : ℕ) + 1 : ℕ) : ℤ)) =
        (ShiftMatrix (α := α) n 0 (n - 1) ^ ((k : ℕ) : ℤ)) @ ShiftMatrix (α := α) n 0 (n - 1) := by
      rw [show (ShiftMatrix (α := α) n 0 (n - 1) ^ (((k : ℕ) + 1 : ℕ) : ℤ)) =
        Tensor.MatPow (ShiftMatrix (α := α) n 0 (n - 1)) (((k : ℕ) + 1 : ℕ) : ℤ) from rfl,
        show (ShiftMatrix (α := α) n 0 (n - 1) ^ ((k : ℕ) : ℤ)) =
        Tensor.MatPow (ShiftMatrix (α := α) n 0 (n - 1)) ((k : ℕ) : ℤ) from rfl]
      simp only [Tensor.MatPow]
      rw [if_pos (by omega : (((k : ℕ) + 1 : ℕ) : ℤ) ≥ 0), if_pos (by omega : ((k : ℕ) : ℤ) ≥ 0)]
      rw [show ((((k : ℕ) + 1 : ℕ) : ℤ)).toNat = k + 1 from by rfl, show (((k : ℕ) : ℤ)).toNat = k from by rfl]
      exact MatProd.eq.DotMatProd (f := fun _ => ShiftMatrix (α := α) n 0 (n - 1))
    rw [hpow]
    apply (GetDot.eq.Sum_MulGetS (ShiftMatrix (α := α) n 0 (n - 1) ^ ((k : ℕ) : ℤ))
      (ShiftMatrix (α := α) n 0 (n - 1)) i j).trans
    have hx : ((i : ℕ) + k) % n < n := Nat.mod_lt _ h
    obtain ⟨a, ha⟩ : ∃ a : Fin n, (a : ℕ) = ((i : ℕ) + k) % n := ⟨⟨_, hx⟩, rfl⟩
    have hmul_one : ∀ X : Tensor α [], (↑(1 : ℕ) : Tensor α []) * X = X := by
      intro X
      erw [Nat.cast_one, Tensor.Mul]
      apply one_mul
    rw [Finset.sum_eq_single a]
    ·
      have hiha := ih a
      have hsa := GetShiftMatrix.eq.ModAddOne.fin (α := α) n h a j
      rw [hiha, ha]
      simp only [id, Delta.eq.Ite, if_true]
      have hmod : (((a : ℕ) + 1) % n) = (((i : ℕ) + (k + 1)) % n) := by
        rw [ha, Nat.mod_add_mod, Nat.add_assoc]
      exact (hmul_one _).trans (hsa.trans (by simp only [Delta.eq.Ite, hmod]; rfl))
    ·
      intro c _ hc
      have hiha := ih c
      rw [hiha]
      simp only [id, Delta.eq.Ite]
      rw [if_neg (fun hcon => hc (Fin.ext (hcon.symm.trans ha.symm)))]
      apply Tensor.EqMul0_0.nat
    ·
      intro hc
      exact absurd (Finset.mem_univ _) hc


-- created on 2026-09-11
