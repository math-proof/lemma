/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

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
public import Def.NumberTheory.RothAuxiliary
public section

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
