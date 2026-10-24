import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Localization.Away.Basic

namespace Ihara

open Matrix

open scoped MatrixGroups

abbrev ZAway (q : ℕ) : Type := Localization.Away (q : ℤ)

variable (N q : ℕ)

def Gamma0Away : Subgroup (SL(2, ZAway q)) where
  carrier := { g | (N : ZAway q) ∣ g 1 0 }
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    change (N : ZAway q) ∣ (1 : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change (N : ZAway q) ∣ (a.1 * b.1) 1 0
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact dvd_neg.mpr ha

theorem mem_Gamma0Away {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ (N : ZAway q) ∣ g 1 0 :=
  Iff.rfl

theorem mem_Gamma0Away_iff_algebraMap {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ algebraMap ℤ (ZAway q) (N : ℤ) ∣ g 1 0 := by
  have h : algebraMap ℤ (ZAway q) (N : ℤ) = (N : ZAway q) := by simp
  rw [mem_Gamma0Away, h]

def wMat : Matrix (Fin 2) (Fin 2) (ZAway q) := !![1, 0; 0, (q : ZAway q)]

noncomputable def wMatInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![1, 0; 0, IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)]

theorem q_mul_invSelf :
    (q : ZAway q) * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) = 1 := by
  simpa using IsLocalization.Away.mul_invSelf (S := ZAway q) ((q : ℕ) : ℤ)

theorem invSelf_mul_q :
    IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) * (q : ZAway q) = 1 := by
  rw [mul_comm]; exact q_mul_invSelf q

theorem wMat_mul_wMatInv : wMat q * wMatInv q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]

theorem wMatInv_mul_wMat : wMatInv q * wMat q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]

noncomputable def wConjFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMatInv q * γ.1 * wMat q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMatInv_mul_wMat, det_one]⟩

noncomputable def wConjInvFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMat q * γ.1 * wMatInv q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMat_mul_wMatInv, det_one]⟩

theorem wConjFun_coe (γ : SL(2, ZAway q)) :
    (wConjFun q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl

theorem wConjInvFun_coe (γ : SL(2, ZAway q)) :
    (wConjInvFun q γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl

noncomputable def wConj : SL(2, ZAway q) ≃* SL(2, ZAway q) where
  toFun := wConjFun q
  invFun := wConjInvFun q
  left_inv γ := Subtype.ext <| by
    rw [wConjInvFun_coe, wConjFun_coe,
      show wMat q * (wMatInv q * γ.1 * wMat q) * wMatInv q
          = (wMat q * wMatInv q) * γ.1 * (wMat q * wMatInv q) by
        simp only [mul_assoc],
      wMat_mul_wMatInv, one_mul, mul_one]
  right_inv γ := Subtype.ext <| by
    rw [wConjFun_coe, wConjInvFun_coe,
      show wMatInv q * (wMat q * γ.1 * wMatInv q) * wMat q
          = (wMatInv q * wMat q) * γ.1 * (wMatInv q * wMat q) by
        simp only [mul_assoc],
      wMatInv_mul_wMat, one_mul, mul_one]
  map_mul' a b := Subtype.ext <| by
    change wMatInv q * (a.1 * b.1) * wMat q
        = wMatInv q * a.1 * wMat q * (wMatInv q * b.1 * wMat q)
    rw [show wMatInv q * a.1 * wMat q * (wMatInv q * b.1 * wMat q)
          = wMatInv q * a.1 * (wMat q * wMatInv q) * (b.1 * wMat q) by
        simp only [mul_assoc],
      wMat_mul_wMatInv, mul_one]
    simp only [mul_assoc]

@[simp]
theorem wConj_coe (γ : SL(2, ZAway q)) :
    (wConj q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl

@[simp]
theorem wConj_symm_coe (γ : SL(2, ZAway q)) :
    ((wConj q).symm γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl

def wMatSwap : Matrix (Fin 2) (Fin 2) (ZAway q) := !![(q : ZAway q), 0; 0, 1]

noncomputable def wMatSwapInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ), 0; 0, 1]

theorem wMatSwap_mul_wMatSwapInv : wMatSwap q * wMatSwapInv q = 1 := by
  rw [wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]

theorem wMatSwapInv_mul_wMatSwap : wMatSwapInv q * wMatSwap q = 1 := by
  rw [wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]

theorem wConj_swap (γ : SL(2, ZAway q)) :
    wMatSwapInv q * γ.1 * wMatSwap q = ((wConj q).symm γ).1 := by
  have hu := invSelf_mul_q q
  rw [wConj_symm_coe]
  induction γ using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    show wMatSwapInv q * !![a, b; c, d] * wMatSwap q
        = wMat q * !![a, b; c, d] * wMatInv q
    rw [wMat, wMatInv, wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.mul_fin_two,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]
    rw [mul_right_comm (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)) a (q : ZAway q), hu]
    simp only [one_mul]
    rw [mul_comm (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)) b,
      mul_comm c (q : ZAway q),
      mul_right_comm (q : ZAway q) d (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)),
      q_mul_invSelf q]
    simp only [one_mul]

end Ihara
