module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Abbrev.Gamma0Away

@[expose] public section

namespace Ihara

open Matrix

open scoped MatrixGroups

variable (N q : ℕ)

def Gamma0Away : Subgroup (SL(2, ZAway q)) where
  carrier := { g | (N : ZAway q) ∣ g 1 0 }
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    change (N : ZAway q) ∣ (1 : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    change (N : ZAway q) ∣ (a.1 * b.1) 1 0
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact dvd_neg.mpr ha

def wMat : Matrix (Fin 2) (Fin 2) (ZAway q) := !![1, 0; 0, (q : ZAway q)]

noncomputable def wMatInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![1, 0; 0, IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)]

noncomputable def wConjFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMatInv q * γ.1 * wMat q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMatInv_mul_wMat, det_one]⟩

noncomputable def wConjInvFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMat q * γ.1 * wMatInv q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMat_mul_wMatInv, det_one]⟩

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

def wMatSwap : Matrix (Fin 2) (Fin 2) (ZAway q) := !![(q : ZAway q), 0; 0, 1]

noncomputable def wMatSwapInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ), 0; 0, 1]

end Ihara

end
