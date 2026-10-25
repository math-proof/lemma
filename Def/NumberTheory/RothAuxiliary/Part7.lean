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
import Theorem.NumberTheory.RothAuxiliary.Part5
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

def rothVanishesBelow {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r)
    (x : Fin m → ℝ) (t : ℝ) : Prop :=
  ∀ i, rothWeight r i < t → rothHasseEval c i x = 0

noncomputable def rothDenProduct {m : ℕ} (q : Fin m → ℚ)
    (r : Fin m → ℕ) : ℕ :=
  ∏ h, (q h).den ^ r h

noncomputable def rothClearEval {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (q : Fin m → ℚ) (r : Fin m → ℕ) : ℤ :=
  ∑ d ∈ P.support, P.coeff d *
    ∏ h, (q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)

def rothRidoutExponent {m : ℕ} {ι : Type*} (r : Fin m → ℕ)
    (a b : Fin m → ι → ℕ) (k : RothMvIndex m) (l : ι) : ℕ :=
  ∑ h, (a h l * k h + b h l * (r h - k h))

noncomputable def rothIntPolynomial (α : ℝ) : ℤ[X] :=
  IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)

noncomputable def rothIntegralPolynomial (α : ℝ) : ℤ[X] :=
  (rothIntPolynomial α).integralNormalization

noncomputable def rothCoordinateBase (α : ℝ) : ℕ :=
  max (rothIntPolynomial α).leadingCoeff.natAbs
    (rothPolyL1 (rothIntegralPolynomial α) + 1)

noncomputable def rothScaledPowerCoord (α : ℝ) (S n : ℕ) : ℤ[X] :=
  Polynomial.C ((rothIntPolynomial α).leadingCoeff ^ (S - n)) *
    rothPowerCoord (rothIntegralPolynomial α) n

noncomputable def rothTermDegree {m : ℕ} {r : Fin m → ℕ}
    (i j : RothBox r) : ℕ :=
  ∑ h, ((j h : ℕ) - (i h : ℕ))

noncomputable def rothAuxTerm (α : ℝ) {m : ℕ} {r : Fin m → ℕ}
    (i j : RothBox r) : ℤ[X] :=
  Polynomial.C (∏ h, (Nat.choose (j h) (i h) : ℤ)) *
    rothScaledPowerCoord α (∑ h, r h) (rothTermDegree i j)

noncomputable def rothAuxMatrix (α : ℝ) {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :
    Matrix (RothLowIndex r γ × Fin (rothIntegralPolynomial α).natDegree)
      (RothBox r) ℤ :=
  fun u j ↦ (rothAuxTerm α u.1.1 j).coeff u.2

noncomputable def rothRidoutAuxMatrix (α : ℝ) {m : ℕ}
    (r : Fin m → ℕ) (γ : ℝ) :
    Matrix (RothLowIndex r γ × Fin ((rothIntegralPolynomial α).natDegree + 2))
      (RothBox r) ℤ :=
  fun u j ↦
    Fin.lastCases
      (if j = rothRidoutBoxComplement r u.1.1 then 1 else 0)
      (fun v ↦ Fin.lastCases
        (if j = u.1.1 then 1 else 0)
        (fun k ↦ rothAuxMatrix α r γ (u.1, k) j) v) u.2

noncomputable def rothAuxCombination (α : ℝ) {m : ℕ} {r : Fin m → ℕ}
    (i : RothBox r) (c : RothCoeff r) : ℤ[X] :=
  ∑ j, Polynomial.C (c j) * rothAuxTerm α i j

end MathlibExt.NumberTheory.RothAuxiliary
