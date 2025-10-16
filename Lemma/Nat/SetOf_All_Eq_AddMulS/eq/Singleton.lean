import Lemma.Algebra.Mul_Sub.eq.SubMulS
import Lemma.Algebra.GeSubSMul.of.Ge
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.AddAdd
import Lemma.Algebra.Mul2.eq.Add
import Lemma.Int.EqAdd.is.Eq_Sub
import Lemma.Algebra.EqAdd.of.Eq_Sub.Le
import Lemma.Algebra.AddSub.eq.SubAdd
import Lemma.Algebra.SubAdd.eq.AddSub.of.Le
import Lemma.Algebra.SubMul.eq.MulSub_1
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Algebra.Eq_Add.of.EqSub.Le
import Lemma.Nat.Fib.eq.AddFibS.of.Ge_2
open Algebra Nat Int


private def G (n : ℕ) := fib (3 * n)


-- Modus Ponens
private lemma mp
  {a b : ℤ}
-- given
  (h : ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2)) :
-- imply
  a = 4 ∧ b = 1 := by
-- proof
  have h₀ := h 2 (by rfl)
  have h₁ := h 3 (by decide)
  simp [G, fib] at h₀ h₁
  constructor <;> omega


-- Modus Ponens Reverse
private lemma mpr
  {a b : ℤ}
-- given
  (h : a = 4 ∧ b = 1) :
-- imply
  ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2) := by
-- proof
  let ⟨h₀, h₁⟩ := h
  rw [h₀, h₁]
  intro n hn
  simp [G]
  norm_cast
  rw [Mul_Sub.eq.SubMulS.nat, Mul_Sub.eq.SubMulS.nat]
  norm_num
  norm_num
  rw [Fib.eq.AddFibS.of.Ge_2 (n := 3 * n)]
  ·
    rw [Fib.eq.AddFibS.of.Ge_2 (n := 3 * n - 1)]
    ·
      rw [SubSub.eq.Sub_Add, SubSub.eq.Sub_Add]
      norm_num
      rw [AddAdd.comm]
      rw [Add.eq.Mul2]
      rw [EqAdd.of.Eq_Sub.Le]
      ·
        rw [SubAdd.eq.AddSub.of.Le]
        ·
          rw [SubMul.eq.MulSub_1.nat]
          norm_num
          have := GeSubSMul.of.Ge hn 3 2
          rw [Fib.eq.AddFibS.of.Ge_2 (n := 3 * n - 2)]
          ·
            rw [SubSub.eq.Sub_Add, SubSub.eq.Sub_Add]
            norm_num
            rw [Mul_Add.eq.AddMulS]
            rw [EqAdd.of.Eq_Sub.Le.left]
            ·
              rw [SubAdd.eq.AddSub.of.Le]
              ·
                rw [SubMulS.eq.MulSub.nat]
                norm_num
                rw [Fib.eq.AddFibS.of.Ge_2 (n := 3 * n - 3)]
                ·
                  rw [SubSub.eq.Sub_Add, SubSub.eq.Sub_Add]
                  norm_num
                  rw [AddAdd.eq.Add_Add]
                  apply Eq_Add.of.EqSub.Le.left
                  ·
                    rw [SubMul.eq.MulSub_1.nat]
                    norm_num
                    rw [Fib.eq.AddFibS.of.Ge_2 (n := 3 * n - 4)]
                    ·
                      rw [SubSub.eq.Sub_Add, SubSub.eq.Sub_Add]
                    ·
                      have := GeSubSMul.of.Ge hn 3 4
                      linarith
                  ·
                    linarith
                ·
                  have := GeSubSMul.of.Ge hn 3 3
                  linarith
              ·
                linarith
            linarith
          ·
            linarith
        ·
          linarith
      ·
        linarith
    ·
      have := GeSubSMul.of.Ge hn 3 1
      linarith
  ·
    linarith


@[main]
private lemma main:
-- imply
  {((a : ℤ), (b : ℤ)) | ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2)} = {(4, 1)} := by
-- proof
  ext ⟨a, b⟩
  constructor <;>
    rintro h
  -- Forward direction: If (a, b) satisfies the recurrence, then (a, b) = (4, 1)
  ·
    have := mp h
    simp_all
  -- Reverse direction: If (a, b) = (4, 1), then the recurrence holds
  ·
    apply mpr
    -- simp at h
    simp_all


-- created on 2025-03-31
