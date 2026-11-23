module

public import Class.AlgebraicCurve_DivisorPushPull
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Algebra.Polynomial.Lifts

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place


section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

private def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in
variable (R) in

def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)

omit [IsDedekindDomain R] [IsFractionRing R F] in
variable (R) in

def centerHeightOneSpectrum (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum R :=
  ⟨center R w hw, Ideal.comap_isPrime _ _, center_ne_bot w hw⟩

end Chart

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (F') in

@[reducible] def valuationSubringAlgebra (v : Place K F) : Algebra v.toValuationSubring F' :=
  ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra

section Setup

variable (v : Place K F)

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in

end Setup

section Center

variable {v : Place K F} {w : Place K F'}

omit [FiniteDimensional F F'] in

variable [IsDedekindDomain (integralClosure v.toValuationSubring F')]
variable [IsFractionRing (integralClosure v.toValuationSubring F') F']

variable (F' v) in

def fiberCenter (hw : w.restrict F = v) : HeightOneSpectrum (integralClosure v.toValuationSubring F') :=
  centerHeightOneSpectrum (integralClosure v.toValuationSubring F') w (forall_mem_of_restrict_eq hw)

omit [FiniteDimensional F F'] in

end Center

section Bijection

variable {v : Place K F}
variable [IsDedekindDomain (integralClosure v.toValuationSubring F')]
variable [IsFractionRing (integralClosure v.toValuationSubring F') F']


def placeOfPrime (P : HeightOneSpectrum (integralClosure v.toValuationSubring F')) : Place K F' where
  toValuationSubring := HeightOneSpectrum.valuationSubringAtPrime F' P
  algebraMap_mem' := fun a => by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap K F' a = algebraMap (integralClosure v.toValuationSubring F') F'
        (algebraMap v.toValuationSubring (integralClosure v.toValuationSubring F')
          (algebraMap K v.toValuationSubring a)) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F',
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring F,
        ← IsScalarTower.algebraMap_apply K F F']
    rw [h1]
    exact P.valuation_le_one _
  ne_top' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := by
    infer_instance

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in

end Bijection

section Fiber

variable (v : Place K F)
variable [IsDedekindDomain (integralClosure v.toValuationSubring F')]
variable [IsFractionRing (integralClosure v.toValuationSubring F') F']


variable (F') in

def fiberEquiv :
    {w : Place K F' // w.restrict F = v} ≃ HeightOneSpectrum (integralClosure v.toValuationSubring F') where
  toFun w := fiberCenter F' v w.2
  invFun P := ⟨placeOfPrime P, restrict_placeOfPrime P⟩
  left_inv w := Subtype.ext (eq_of_fiberCenter_eq (restrict_placeOfPrime _) w.2
    (fiberCenter_placeOfPrime (fiberCenter F' v w.2)))
  right_inv P := fiberCenter_placeOfPrime P

variable (F') in

def fiberOver : Finset (Place K F') :=
  (finite_setOf_restrict_eq (F' := F') v).toFinset

end Fiber

end Place

end AlgebraicCurve

end

end
