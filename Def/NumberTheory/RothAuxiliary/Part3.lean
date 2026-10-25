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
import Structure.NumberTheory.RothAuxiliary.Part2
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

noncomputable def rothBoxIndex {m : ℕ} {r : Fin m → ℕ}
    (j : RothBox r) : RothMvIndex m :=
  Finsupp.equivFunOnFinite.symm fun h ↦ j h

noncomputable def rothMvOfCoeff {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r) :
    MvPolynomial (Fin m) ℤ :=
  ∑ j, MvPolynomial.monomial (rothBoxIndex j) (c j)

noncomputable def rothPowerCoord (g : ℤ[X]) : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      Polynomial.X * rothPowerCoord g n -
        Polynomial.C ((rothPowerCoord g n).coeff (g.natDegree - 1)) * g

noncomputable def rothHasseEval {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMultiIndex m) (x : Fin m → R) : R :=
  ∑ j, (c j : R) * ∏ h, (Nat.choose (j h) (i h) : R) * x h ^ (j h - i h)

noncomputable def rothEval {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (x : Fin m → R) : R :=
  ∑ j, (c j : R) * ∏ h, x h ^ (j h : ℕ)

noncomputable def rothWeight {m : ℕ} (r : Fin m → ℕ)
    (i : RothMultiIndex m) : ℝ :=
  ∑ h, (i h : ℝ) / r h

def rothRidoutBoxComplement {m : ℕ} (r : Fin m → ℕ) (j : RothBox r) :
    RothBox r :=
  fun h ↦ ⟨r h - j h, Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

noncomputable def rothCentered {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) (h : Fin m) : ℝ :=
  (j h : ℝ) / r h - 1 / 2

noncomputable def rothCenteredSum {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) : ℝ :=
  ∑ h, rothCentered r j h

def rothFlip {m : ℕ} (r : Fin m → ℕ) (h : Fin m) (j : RothBox r) :
    RothBox r :=
  Function.update j h ⟨r h - j h, Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

end MathlibExt.NumberTheory.RothAuxiliary
