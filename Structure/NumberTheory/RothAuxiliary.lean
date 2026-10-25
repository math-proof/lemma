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
import Def.NumberTheory.RothAuxiliary
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

structure RothDeterminantData {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ) where
  k : ℕ
  k_pos : 0 < k
  k_le : k ≤ r (Fin.last n) + 1
  row : Fin k → RothMvIndex n
  row_order : ∀ s, rothMvOrder (row s) ≤ s
  V : MvPolynomial (Fin n) ℤ
  W : ℚ[X]
  U : MvPolynomial (Fin (n + 1)) ℤ
  V_ne : V ≠ 0
  W_ne : W ≠ 0
  U_def : U = rothHasseDet P
    (fun s ↦ rothLastIndex (row s) 0)
    (fun t ↦ rothLastIndex 0 t.val)
  factorization :
    rothLastEquiv ℚ n (MvPolynomial.map (algebraMap ℤ ℚ) U) =
      Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) V) *
        Polynomial.map MvPolynomial.C W
  V_degree : rothDegreeBound V (fun h ↦ k * r h.castSucc)
  U_degree : rothDegreeBound U (fun h ↦ k * r h)
  V_l1 : rothMvL1 V ≤
    k.factorial * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ k
  U_l1 : rothMvL1 U ≤
    k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k

end MathlibExt.NumberTheory.RothAuxiliary
