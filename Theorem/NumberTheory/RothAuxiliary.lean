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
import Def.NumberTheory.RothAuxiliary.Part3
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

theorem rothFlip_apply_same {m : ℕ} (r : Fin m → ℕ) (h : Fin m)
    (j : RothBox r) :
    ((rothFlip r h j) h : ℕ) = r h - j h := by
  simp [rothFlip]

theorem rothFlip_apply_ne {m : ℕ} (r : Fin m → ℕ) {h k : Fin m}
    (hhk : k ≠ h) (j : RothBox r) :
    rothFlip r h j k = j k := by
  simp [rothFlip, hhk]

theorem rothFlip_involutive {m : ℕ} (r : Fin m → ℕ) (h : Fin m) :
    Function.Involutive (rothFlip r h) := by
  intro j
  funext k
  by_cases hkh : k = h
  · subst k
    apply Fin.ext
    rw [rothFlip_apply_same, rothFlip_apply_same]
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  · rw [rothFlip_apply_ne r hkh, rothFlip_apply_ne r hkh]

end MathlibExt.NumberTheory.RothAuxiliary
