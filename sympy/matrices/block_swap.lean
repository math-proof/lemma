import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Block

/-! Determinant of a block matrix with a zero block on the anti-diagonal: rows split as `a ⊕ b`, columns as `b ⊕ a`; the column block swap is the rotation `finRotate^a` with sign `(-1)^(a*b)`. -/

open Matrix Equiv

namespace Matrix.BlockSwap

/-- square view of a block matrix whose rows split as `a ⊕ b` and whose columns split as `b ⊕ a`. -/
def sq {R : Type*} {a b : ℕ} (M : Matrix (Fin a ⊕ Fin b) (Fin b ⊕ Fin a) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  Matrix.of fun i j => M (finSumFinEquiv.symm i) (finSumFinEquiv.symm (finCongr (Nat.add_comm a b) j))

/-- the column permutation `τ` (rotation by `a`). -/
def tau (a b : ℕ) : Perm (Fin (a + b)) :=
  ((finCongr (Nat.add_comm a b)).trans finSumFinEquiv.symm).trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

theorem finRotate_pow_val (N a : ℕ) (v : Fin (N + 1)) :
    (((finRotate (N + 1)) ^ a) v : ℕ) = (v + a) % (N + 1) := by
  induction a with
  | zero => simp [Nat.mod_eq_of_lt v.2]
  | succ a ih =>
    rw [pow_succ', Perm.mul_apply, finRotate_apply, Fin.val_add, ih]
    simp only [Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem tau_eq (a b : ℕ) (hN : 0 < a + b) :
    tau a b = ((finCongr (show a + b - 1 + 1 = a + b by omega)).symm.trans
      ((finRotate (a + b - 1 + 1)) ^ a)).trans (finCongr (show a + b - 1 + 1 = a + b by omega)) := by
  have e : a + b - 1 + 1 = a + b := by omega
  ext v
  simp only [tau, Equiv.trans_apply, finCongr_apply, finCongr_symm, Fin.val_cast]
  rw [finRotate_pow_val, Fin.val_cast]
  rcases lt_or_ge (v : ℕ) b with h | h
  · have : (finSumFinEquiv.symm (Fin.cast (Nat.add_comm a b) v) : Fin b ⊕ Fin a) = Sum.inl ⟨v, h⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp
    rw [this]; simp [e, Nat.mod_eq_of_lt (show (v : ℕ) + a < a + b by omega)]; omega
  · have : (finSumFinEquiv.symm (Fin.cast (Nat.add_comm a b) v) : Fin b ⊕ Fin a) = Sum.inr ⟨v - b, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp; omega
    rw [this]; simp [e]
    rw [show (v : ℕ) + a = (v - b) + (a + b) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem sign_tau (a b : ℕ) : Perm.sign (tau a b) = (-1) ^ (a * b) := by
  rcases Nat.eq_zero_or_pos (a + b) with h0 | hN
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have : tau 0 0 = 1 := Equiv.ext (fun v => v.elim0)
    rw [this, map_one]
    rfl
  · rw [tau_eq a b hN, Perm.sign_symm_trans_trans, map_pow, sign_finRotate, ← pow_mul]
    have key : ∀ t : ℕ, t + 1 = a + b → (-1 : ℤˣ) ^ (t * a) = (-1) ^ (a * b) := by
      intro t ht
      rcases a with _ | a
      · simp
      · have h3 : t * (a + 1) = a * (a + 1) + (a + 1) * b := by
          obtain rfl : t = a + b := by omega
          ring
        rw [h3, pow_add, (Nat.even_mul_succ_self a).neg_one_pow, one_mul]
    exact key _ (by omega)

theorem det_sq {R : Type*} [CommRing R] {a b : ℕ} (P : Matrix (Fin a) (Fin b) R) (Q : Matrix (Fin a) (Fin a) R)
    (C : Matrix (Fin b) (Fin b) R) (S : Matrix (Fin b) (Fin a) R) :
    (sq (Matrix.fromBlocks P Q C S)).det = (-1) ^ (a * b) * (Matrix.fromBlocks Q P S C).det := by
  have h : sq (Matrix.fromBlocks P Q C S) =
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q P S C)).submatrix id (tau a b) := by
    ext i j
    simp only [sq, tau, Matrix.of_apply, Matrix.submatrix_apply, Matrix.reindex_apply, id, Equiv.trans_apply,
      finCongr_apply, Equiv.symm_apply_apply]
    rcases finSumFinEquiv.symm i with r | r <;>
      rcases hc : finSumFinEquiv.symm (Fin.cast (Nat.add_comm a b) j) with k | k <;> simp
  rw [h, Matrix.det_permute', Matrix.det_reindex_self, sign_tau]
  push_cast
  ring

theorem det_zero₁₁ {R : Type*} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R)
    (C : Matrix (Fin b) (Fin b) R) (D : Matrix (Fin b) (Fin a) R) :
    (sq (Matrix.fromBlocks 0 A C D)).det = (-1) ^ (a * b) * A.det * C.det := by
  rw [det_sq, Matrix.det_fromBlocks_zero₁₂, mul_assoc]

theorem det_zero₂₂ {R : Type*} [CommRing R] {a b : ℕ} (P : Matrix (Fin a) (Fin b) R) (A : Matrix (Fin a) (Fin a) R)
    (C : Matrix (Fin b) (Fin b) R) :
    (sq (Matrix.fromBlocks P A C 0)).det = (-1) ^ (a * b) * A.det * C.det := by
  rw [det_sq, Matrix.det_fromBlocks_zero₂₁, mul_assoc]

end Matrix.BlockSwap
