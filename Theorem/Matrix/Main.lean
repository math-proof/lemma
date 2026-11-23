module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Abbrev.Gamma0Away

public section

namespace Ihara

open Matrix

open scoped MatrixGroups

variable (N q : ℕ)


public theorem mem_Gamma0Away {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ (N : ZAway q) ∣ g 1 0 :=
  Iff.rfl


public theorem mem_Gamma0Away_iff_algebraMap {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ algebraMap ℤ (ZAway q) (N : ℤ) ∣ g 1 0 := by
  have h : algebraMap ℤ (ZAway q) (N : ℤ) = (N : ZAway q) := by simp
  rw [mem_Gamma0Away, h]


public theorem q_mul_invSelf :
    (q : ZAway q) * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) = 1 := by
  simpa using IsLocalization.Away.mul_invSelf (S := ZAway q) ((q : ℕ) : ℤ)


public theorem invSelf_mul_q :
    IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) * (q : ZAway q) = 1 := by
  rw [mul_comm]; exact q_mul_invSelf q


public theorem wMat_mul_wMatInv : wMat q * wMatInv q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]


public theorem wMatInv_mul_wMat : wMatInv q * wMat q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]


public theorem wConjFun_coe (γ : SL(2, ZAway q)) :
    (wConjFun q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl


public theorem wConjInvFun_coe (γ : SL(2, ZAway q)) :
    (wConjInvFun q γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl


@[simp]
public theorem wConj_coe (γ : SL(2, ZAway q)) :
    (wConj q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl


@[simp]
public theorem wConj_symm_coe (γ : SL(2, ZAway q)) :
    ((wConj q).symm γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl


public theorem wMatSwap_mul_wMatSwapInv : wMatSwap q * wMatSwapInv q = 1 := by
  rw [wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]


public theorem wMatSwapInv_mul_wMatSwap : wMatSwapInv q * wMatSwap q = 1 := by
  rw [wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]


public theorem wConj_swap (γ : SL(2, ZAway q)) :
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
