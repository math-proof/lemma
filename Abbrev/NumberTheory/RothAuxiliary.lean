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
@[expose] public section

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

abbrev RothMultiIndex (m : ℕ) := Fin m → ℕ

abbrev RothBox {m : ℕ} (r : Fin m → ℕ) := ∀ h, Fin (r h + 1)

abbrev RothCoeff {m : ℕ} (r : Fin m → ℕ) := RothBox r → ℤ

abbrev RothMvIndex (m : ℕ) := Fin m →₀ ℕ

end MathlibExt.NumberTheory.RothAuxiliary
