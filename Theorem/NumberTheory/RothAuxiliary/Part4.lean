module
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.SiegelsLemma
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic
public import Abbrev.NumberTheory.RothAuxiliary.Part2
set_option maxHeartbeats 999999
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/
namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

theorem roth_low_equation_card_lt {m d : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ)
    (hparam : (d : ℝ) < 4 * m * γ ^ 2) :
    Fintype.card (RothLowIndex r γ × Fin d) < Fintype.card (RothBox r) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  by_cases hL : (rothLowIndices r γ).card = 0
  · simp only [hL, zero_mul]
    exact Fintype.card_pos_iff.mpr
      ⟨fun h ↦ ⟨0, Nat.succ_pos (r h)⟩⟩
  · have hLpos : (0 : ℝ) < (rothLowIndices r γ).card := by
      exact_mod_cast Nat.pos_of_ne_zero hL
    have hstrict :
        (d : ℝ) * (rothLowIndices r γ).card <
          (4 * m * γ ^ 2) * (rothLowIndices r γ).card :=
      mul_lt_mul_of_pos_right hparam hLpos
    have hbound := roth_low_indices_card_bound hr hm hγ
    have hreal :
        ((d * (rothLowIndices r γ).card : ℕ) : ℝ) <
          Fintype.card (RothBox r) := by
      norm_num only [Nat.cast_mul]
      exact hstrict.trans_le hbound
    have hnat : d * (rothLowIndices r γ).card < Fintype.card (RothBox r) := by
      exact_mod_cast hreal
    simpa [mul_comm] using hnat

end MathlibExt.NumberTheory.RothAuxiliary
