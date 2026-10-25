/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic
import Def.NumberTheory.RothAuxiliary.Part4
set_option maxHeartbeats 999999

open scoped BigOperators

/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/


namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

theorem rothCentered_flip_same {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (h : Fin m) (j : RothBox r) :
    rothCentered r (rothFlip r h j) h = -rothCentered r j h := by
  unfold rothCentered
  rw [rothFlip_apply_same]
  have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  rw [Nat.cast_sub hjle]
  have hrR : (0 : ℝ) < r h := by exact_mod_cast hr h
  field_simp
  ring

theorem rothCentered_flip_ne {m : ℕ} {r : Fin m → ℕ}
    {h k : Fin m} (hhk : k ≠ h) (j : RothBox r) :
    rothCentered r (rothFlip r h j) k = rothCentered r j k := by
  simp only [rothCentered, rothFlip_apply_ne r hhk]

theorem rothCentered_cross_sum {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) {h k : Fin m} (hhk : h ≠ k) :
    ∑ j : RothBox r, rothCentered r j h * rothCentered r j k = 0 := by
  have hreindex := Equiv.sum_comp (rothFlipEquiv r h)
    (fun j : RothBox r ↦ rothCentered r j h * rothCentered r j k)
  have hkh : k ≠ h := Ne.symm hhk
  have hneg :
      (∑ j : RothBox r,
          rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
        -(∑ j : RothBox r, rothCentered r j h * rothCentered r j k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [rothCentered_flip_same hr, rothCentered_flip_ne hkh]
    ring
  change
    (∑ j : RothBox r,
        rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
      ∑ j : RothBox r, rothCentered r j h * rothCentered r j k at hreindex
  rw [hneg] at hreindex
  linarith

theorem rothCentered_second_moment_le {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) :
    ∑ j : RothBox r, rothCenteredSum r j ^ 2 ≤
      (m : ℝ) * Fintype.card (RothBox r) / 4 := by
  have hexpand :
      (∑ j : RothBox r, rothCenteredSum r j ^ 2) =
        ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
          rothCentered r j h * rothCentered r j k := by
    calc
      (∑ j : RothBox r, rothCenteredSum r j ^ 2) =
          ∑ j : RothBox r, ∑ h : Fin m, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro j _hj
        unfold rothCenteredSum
        rw [pow_two, Finset.sum_mul_sum]
      _ = ∑ h : Fin m, ∑ j : RothBox r, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := Finset.sum_comm
      _ = ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro h _hh
        exact Finset.sum_comm
  rw [hexpand]
  calc
    (∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
        rothCentered r j h * rothCentered r j k) ≤
        ∑ h : Fin m, ∑ k : Fin m,
          if h = k then (Fintype.card (RothBox r) : ℝ) / 4 else 0 := by
      gcongr with h k
      by_cases hhk : h = k
      · subst k
        simpa [pow_two] using rothCentered_sq_sum_le hr h
      · simp only [hhk, ↓reduceIte]
        rw [rothCentered_cross_sum hr hhk]
    _ = (m : ℝ) * Fintype.card (RothBox r) / 4 := by
      simp
      ring

end MathlibExt.NumberTheory.RothAuxiliary
