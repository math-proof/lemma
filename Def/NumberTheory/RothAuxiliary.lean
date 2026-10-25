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
import Abbrev.NumberTheory.RothAuxiliary
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

noncomputable def rothMvHasse {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (P : MvPolynomial (Fin m) R) : MvPolynomial (Fin m) R :=
  P.coeff.sum fun j c ↦
    MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c)

noncomputable def rothTranslate {R : Type*} [CommRing R] :
    (m : ℕ) → (Fin m → R) →
      MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R
  | 0, _ => RingHom.id _
  | n + 1, x =>
      (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.toRingHom.comp
        ((Polynomial.mapRingHom (rothTranslate n (fun h ↦ x h.succ))).comp
          ((Polynomial.taylorAlgHom (R := MvPolynomial (Fin n) R)
              (MvPolynomial.C (x 0))).toRingHom.comp
            (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom))

noncomputable def rothMvWeight {m : ℕ} (r : Fin m → ℕ)
    (i : RothMvIndex m) : ℝ :=
  ∑ h, (i h : ℝ) / r h

noncomputable def rothRidoutComplement {m : ℕ} (r : Fin m → ℕ)
    (i : RothMvIndex m) : RothMvIndex m :=
  Finsupp.equivFunOnFinite.symm fun h ↦ r h - i h

def rothMvVanishesBelow {m : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) : Prop :=
  ∀ i, rothMvWeight r i < t → (rothTranslate m x P).coeff i = 0

noncomputable def rothHasseDet {m k : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (u v : Fin k → RothMvIndex m) :
    MvPolynomial (Fin m) R :=
  Matrix.det fun s t ↦ rothMvHasse (u s + v t) P

noncomputable def rothPolyDerivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (n : ℕ) : Fin k → K[X] :=
  fun j ↦ Polynomial.derivative^[n] (f j)

def rothPolyJetRows {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (s : ℕ) : Set (Fin k → K[X]) :=
  {v | ∃ n ≤ s, v = rothPolyDerivativeRow f n}

noncomputable def rothPolyRowDerivative {k : ℕ} {K : Type*} [Field K]
    (v : Fin k → K[X]) : Fin k → K[X] :=
  fun j ↦ (v j).derivative

noncomputable def rothPolyWronskianRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) : Fin (k + 1) → K[X] :=
  fun j ↦ Polynomial.wronskian (f 0) (f j)

noncomputable def rothPolyWronskianDerivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) : Fin (k + 1) → K[X] :=
  fun j ↦ Polynomial.derivative^[n] (Polynomial.wronskian (f 0) (f j))

def rothKroneckerEncode {m : ℕ} (D : ℕ) (i : Fin m → ℕ) : ℕ :=
  ∑ h : Fin m, i h * D ^ (h : ℕ)

noncomputable def rothKronecker {m : ℕ} {K : Type*} [Field K] (D : ℕ) :
    MvPolynomial (Fin m) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun h ↦ Polynomial.X ^ D ^ (h : ℕ))

def rothKroneckerBounded {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) : Prop :=
  ∀ i ∈ P.support, ∀ h, i h < D

def rothMvOrder {m : ℕ} (i : RothMvIndex m) : ℕ :=
  ∑ h, i h

noncomputable def rothKronHasseRow {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (i : RothMvIndex m) : Fin k → ℚ[X] :=
  fun j ↦ rothKronecker D (rothMvHasse i (f j))

def rothKronHasseJetRows {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (s : ℕ) : Set (Fin k → ℚ[X]) :=
  {v | ∃ i : RothMvIndex m, rothMvOrder i ≤ s ∧ v = rothKronHasseRow D f i}

def rothFinsuppL1 {α : Type*} (f : α →₀ ℤ) : ℕ :=
  ∑ a ∈ f.support, (f a).natAbs

def rothMvL1 {m : ℕ} (P : MvPolynomial (Fin m) ℤ) : ℕ :=
  rothFinsuppL1 P.coeff

def rothDegreeBound {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (r : Fin m → ℕ) : Prop :=
  ∀ j ∈ P.support, ∀ h, j h ≤ r h

def rothDegreeBoundOver {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (r : Fin m → ℕ) : Prop :=
  ∀ j ∈ P.support, ∀ h, j h ≤ r h

noncomputable def rothLastEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft R (Fin n))

noncomputable def rothLastIndex {n : ℕ} (i : RothMvIndex n) (a : ℕ) :
    RothMvIndex (n + 1) :=
  (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)

noncomputable def rothLastTail {n : ℕ} (d : RothMvIndex (n + 1)) :
    RothMvIndex n :=
  ((Finsupp.equivCongrLeft finSuccEquivLast) d).some

noncomputable def rothLastSlice {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n) : ℤ[X] :=
  ∑ a ∈ (rothLastEquiv ℤ n P).support,
    Polynomial.monomial a (((rothLastEquiv ℤ n P).coeff a).coeff i)

end MathlibExt.NumberTheory.RothAuxiliary
