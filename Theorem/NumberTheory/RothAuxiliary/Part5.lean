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
import Def.NumberTheory.RothAuxiliary.Part6
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

theorem roth_low_equation_twice_card_le {m d : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ)
    (hparam : (d : ℝ) ≤ 2 * m * γ ^ 2) :
    2 * Fintype.card (RothLowIndex r γ × Fin d) ≤ Fintype.card (RothBox r) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  have hbound := roth_low_indices_card_bound hr hm hγ
  have hreal :
      ((2 * ((rothLowIndices r γ).card * d) : ℕ) : ℝ) ≤
        Fintype.card (RothBox r) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 : ℝ) * ((rothLowIndices r γ).card * d) =
          (2 * d) * (rothLowIndices r γ).card := by ring
      _ ≤ (4 * m * γ ^ 2) * (rothLowIndices r γ).card := by
        have hcoef : (2 : ℝ) * d ≤ 4 * m * γ ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ Fintype.card (RothBox r) := hbound
  exact_mod_cast hreal

end MathlibExt.NumberTheory.RothAuxiliary
