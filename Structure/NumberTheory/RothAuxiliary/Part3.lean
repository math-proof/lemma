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
import Theorem.NumberTheory.RothAuxiliary.Part6
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

structure RothLemmaInput (n : ℕ) (δ : ℝ) (Q R : ℕ) where
  P : MvPolynomial (Fin (n + 1)) ℤ
  r : Fin (n + 1) → ℕ
  q : Fin (n + 1) → ℚ
  P_ne : P ≠ 0
  P_degree : rothDegreeBound P r
  r_large : ∀ h, R ≤ r h
  den_large : Q ≤ (q 0).den
  den_monotone : Monotone fun h ↦ (q h).den
  r_antitone : Antitone r
  separated : ∀ i : Fin n, (r i.succ : ℝ) ≤ δ * r i.castSucc
  den_power : ∀ h, (q 0).den ^ r 0 ≤ (q h).den ^ r h
  height : (rothMvL1 P : ℝ) ≤ Real.rpow (q 0).den (δ * r 0)

end MathlibExt.NumberTheory.RothAuxiliary
