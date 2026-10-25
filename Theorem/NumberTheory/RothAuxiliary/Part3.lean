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
import Def.NumberTheory.RothAuxiliary.Part5
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

theorem roth_low_indices_card_bound {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ) :
    (4 : ℝ) * m * γ ^ 2 * (rothLowIndices r γ).card ≤
      Fintype.card (RothBox r) := by
  let L := rothLowIndices r γ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpoint : ∀ j ∈ L,
      ((m : ℝ) * γ) ^ 2 ≤ rothCenteredSum r j ^ 2 := by
    intro j hj
    have hjlow := (Finset.mem_filter.mp hj).2
    rw [rothWeight_eq_centeredSum_add] at hjlow
    have hs : rothCenteredSum r j < -((m : ℝ) * γ) := by linarith
    have hmg : 0 < (m : ℝ) * γ := mul_pos hmR hγ
    nlinarith
  have hlow :
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
        ∑ j ∈ L, rothCenteredSum r j ^ 2 := by
    calc
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 =
          ∑ _j ∈ L, ((m : ℝ) * γ) ^ 2 := by simp
      _ ≤ ∑ j ∈ L, rothCenteredSum r j ^ 2 := by
        exact Finset.sum_le_sum fun j hj ↦ hpoint j hj
  have hsubset :
      (∑ j ∈ L, rothCenteredSum r j ^ 2) ≤
        ∑ j : RothBox r, rothCenteredSum r j ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro j _hj _hjL
      positivity
  have hmain :
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
        (m : ℝ) * Fintype.card (RothBox r) / 4 :=
    hlow.trans (hsubset.trans (rothCentered_second_moment_le hr))
  have hmul :
      (m : ℝ) * ((4 : ℝ) * m * γ ^ 2 * L.card) ≤
        (m : ℝ) * Fintype.card (RothBox r) := by
    calc
      (m : ℝ) * ((4 : ℝ) * m * γ ^ 2 * L.card) =
          4 * ((L.card : ℝ) * ((m : ℝ) * γ) ^ 2) := by ring
      _ ≤ 4 * ((m : ℝ) * Fintype.card (RothBox r) / 4) := by
        gcongr
      _ = (m : ℝ) * Fintype.card (RothBox r) := by ring
  exact (mul_le_mul_iff_of_pos_left hmR).mp hmul

end MathlibExt.NumberTheory.RothAuxiliary
