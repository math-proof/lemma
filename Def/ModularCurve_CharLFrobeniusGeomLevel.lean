module

public import Mathlib
public import Theorem.Scheme.IsCurveOver
public import Theorem.Matrix.DivisorPushPull
public import Theorem.Ideal.RatFuncPlaces
public import Theorem.Polynomial.FrobeniusEndo
public import Theorem.ValuationSubring.FrobeniusEndoPic0
public import Theorem.HahnSeries.JqCoeff
public import Theorem.Polynomial.FibrePoly
public import Def.HeckeGalois_EichlerShimura

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve Polynomial Matrix ValuationSubring Ideal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve


section QExpandAlg
variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def qExpandAlgC : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K N
  commutes' r := by
    show qExpand K N (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero]
end QExpandAlg


section DegOneBridge
open AlgebraicCurve Matrix Polynomial ValuationSubring Ideal
variable (K : Type*) [Field K] (N : ℕ) [NeZero N] [IsAlgClosed K]
    [IsCurveOver K (modularFunctionFieldC K N)]

end DegOneBridge

end ModularCurve

noncomputable section

open AlgebraicCurve Polynomial Matrix ValuationSubring Ideal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

section FrobeniusEndomorphism

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

def frobeniusGeomLevelImage : IntermediateField K (LaurentSeries K) :=
  (modularFunctionFieldC K N).map (qExpandAlgC K ℓ)

def frobeniusGeomLevelEquiv :
    (modularFunctionFieldC K N) ≃ₐ[K] (frobeniusGeomLevelImage K N (ℓ := ℓ)) :=
  (modularFunctionFieldC K N).equivMap (qExpandAlgC K ℓ)

omit [CharP K ℓ] in
def frobeniusGeomLevel : modularFunctionFieldC K N →ₐ[K] modularFunctionFieldC K N :=
  (IntermediateField.inclusion (frobeniusGeomLevel_map_le K N data hKr)).comp
    (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).toAlgHom

end FrobeniusEndomorphism

section PurelyInseparable

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

omit [Fact ℓ.Prime] in

end PurelyInseparable

section PlaceLevel

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

@[reducible] def frobImageAlgebra :
    Algebra (frobeniusGeomLevelImage K N (ℓ := ℓ)) (modularFunctionFieldC K N) :=
  (IntermediateField.inclusion (frobeniusGeomLevel_map_le K N data hKr)).toRingHom.toAlgebra

include data hKr in

def frobOnPlacesGeomLevel (w : Place K (modularFunctionFieldC K N)) :
    Place K (modularFunctionFieldC K N) :=
  letI := frobImageAlgebra K N data hKr
  letI := frobImageTower K N data hKr
  letI := frobImageIsIntegral K N data hKr
  (Place.congrEquiv (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).toRingEquiv
    (fun a => (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).commutes a)).symm
    (w.restrict (frobeniusGeomLevelImage K N (ℓ := ℓ)))

open Classical in

def verOnPlacesGeomLevel (u : Place K (modularFunctionFieldC K N)) :
    Place K (modularFunctionFieldC K N) :=
  if h : ∃ w, frobOnPlacesGeomLevel K N data hKr w = u then h.choose else u

end PlaceLevel

section DivisorLevel

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

def frobeniusPushforwardGeomLevel :
    Divisor K (modularFunctionFieldC K N) →+ Divisor K (modularFunctionFieldC K N) :=
  Finsupp.mapDomain.addMonoidHom (frobOnPlacesGeomLevel K N data hKr)

include data hKr in

def frobeniusPullbackGeomLevel :
    Divisor K (modularFunctionFieldC K N) →+ Divisor K (modularFunctionFieldC K N) :=
  Finsupp.liftAddHom fun v =>
    (Finsupp.singleAddHom (verOnPlacesGeomLevel K N data hKr v)).comp
      (AddMonoidHom.mulRight (ℓ : ℤ))

include data hKr in

def heckeFibreGeomLevel :
    Divisor K (modularFunctionFieldC K N) →+ Divisor K (modularFunctionFieldC K N) :=
  frobeniusPushforwardGeomLevel K N data hKr + frobeniusPullbackGeomLevel K N data hKr

end DivisorLevel


end ModularCurve

namespace AlgebraicCurve
namespace Place


section RestrictPriv
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (w : Place K F')


variable [Algebra.IsIntegral F F']

end RestrictPriv

end Place
end AlgebraicCurve

noncomputable section

open AlgebraicCurve Polynomial Matrix ValuationSubring Ideal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

section Package

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end Package


section Ramification

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end Ramification

section NormFormula

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end NormFormula

end ModularCurve

noncomputable section

namespace AlgebraicCurve

section FrobNormHom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} {φ : F →ₐ[K] F}

namespace IsFrobeniusEndo

variable [Fact ℓ.Prime] [CharP F ℓ]

omit [CharP F ℓ] in

def frobNormRingHom (h : IsFrobeniusEndo ℓ φ) : F →+* F where
  toFun := h.frobNorm
  map_one' := h.frobNorm_one
  map_mul' := h.frobNorm_mul
  map_zero' := h.frobNorm_zero
  map_add' := h.frobNorm_add

end IsFrobeniusEndo

end FrobNormHom

section ExtendPlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] {φ : F →ₐ[K] F}

namespace IsFrobeniusEndo

variable (h : IsFrobeniusEndo ℓ φ)

def extendPlace (v : Place K F) : Place K F where
  toValuationSubring := v.toValuationSubring.comap h.frobNormRingHom
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap, frobNormRingHom_apply, h.frobNorm_algebraMap]
    exact pow_mem (v.algebraMap_mem' a) ℓ
  ne_top' := by

    intro htop
    apply v.ne_top'
    refine SetLike.ext fun z => ⟨fun _ => ValuationSubring.mem_top z, fun _ => ?_⟩
    have hz : φ z ∈ v.toValuationSubring.comap h.frobNormRingHom :=
      htop ▸ ValuationSubring.mem_top (φ z)
    rw [ValuationSubring.mem_comap, frobNormRingHom_apply, h.frobNorm_map] at hz
    exact (v.toValuationSubring.pow_mem_iff (Fact.out : ℓ.Prime).pos.ne' z).mp hz
  isPrincipalIdealRing' := by

    letI : Algebra F F := h.frobNormRingHom.toAlgebra
    haveI : Algebra.IsIntegral F F := ⟨h.frobNormRingHom_isIntegral⟩
    exact v.isPrincipalIdealRing_comap (F := F)

end IsFrobeniusEndo

end ExtendPlace

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve Matrix Polynomial ValuationSubring Ideal

section LevelN

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

omit [Fact ℓ.Prime] in

def extendPlaceGeomLevel (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
    (v : Place K (modularFunctionFieldC K N)) : Place K (modularFunctionFieldC K N) :=
  haveI : CharP (modularFunctionFieldC K N) ℓ := charP_modularFunctionFieldC K N
  (isFrobeniusEndo_frobeniusGeomLevel K N data hKr hperf).extendPlace v

include data hKr in

end LevelN

section Consumers

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end Consumers

end ModularCurve

noncomputable section

open AlgebraicCurve Polynomial Matrix ValuationSubring Ideal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

section PlaceLevel

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end PlaceLevel

section Evaluation

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end Evaluation

section Principal

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

end Principal

end ModularCurve

noncomputable section

open AlgebraicCurve Matrix Polynomial ValuationSubring Ideal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

section DegreePlace

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1)

include data hKr hdeg1 in

end DegreePlace

section DegreeDivisor

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1)

include data hKr hdeg1 in

def frobeniusPushforwardGeomLevelDegZero :
    Divisor.degZero (K := K) (F := modularFunctionFieldC K N)
      →+ Divisor.degZero (K := K) (F := modularFunctionFieldC K N) :=
  ((frobeniusPushforwardGeomLevel K N data hKr).domRestrict
    (Divisor.degZero (K := K) (F := modularFunctionFieldC K N))).codRestrict _
    (fun D => frobeniusPushforwardGeomLevel_mem_degZero K N data hKr hdeg1 D.2)

def frobeniusPullbackGeomLevelDegZero :
    Divisor.degZero (K := K) (F := modularFunctionFieldC K N)
      →+ Divisor.degZero (K := K) (F := modularFunctionFieldC K N) :=
  ((frobeniusPullbackGeomLevel K N data hKr).domRestrict
    (Divisor.degZero (K := K) (F := modularFunctionFieldC K N))).codRestrict _
    (fun D => frobeniusPullbackGeomLevel_mem_degZero K N data hKr hdeg1 D.2)

def heckeFibreGeomLevelDegZero :
    Divisor.degZero (K := K) (F := modularFunctionFieldC K N)
      →+ Divisor.degZero (K := K) (F := modularFunctionFieldC K N) :=
  ((heckeFibreGeomLevel K N data hKr).domRestrict
    (Divisor.degZero (K := K) (F := modularFunctionFieldC K N))).codRestrict _
    (fun D => heckeFibreGeomLevel_mem_degZero K N data hKr hdeg1 D.2)

end DegreeDivisor

section Pic0Ops

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
variable (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1)

include data hKr hperf hdeg1 in

def frobeniusPushforwardGeomLevelPic0 :
    Pic0 K (modularFunctionFieldC K N) →+ Pic0 K (modularFunctionFieldC K N) :=
  QuotientAddGroup.map _ _ (frobeniusPushforwardGeomLevelDegZero K N data hKr hdeg1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_frobeniusPushforwardGeomLevel' K N data hKr hperf hD)

def frobeniusPullbackGeomLevelPic0 :
    Pic0 K (modularFunctionFieldC K N) →+ Pic0 K (modularFunctionFieldC K N) :=
  QuotientAddGroup.map _ _ (frobeniusPullbackGeomLevelDegZero K N data hKr hdeg1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_frobeniusPullbackGeomLevel' K N data hKr hperf
      (frobOnPlacesGeomLevel_surjective K N data hKr hperf) hD)

def heckeFibreGeomLevelPic0 :
    Pic0 K (modularFunctionFieldC K N) →+ Pic0 K (modularFunctionFieldC K N) :=
  QuotientAddGroup.map _ _ (heckeFibreGeomLevelDegZero K N data hKr hdeg1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_heckeFibreGeomLevel' K N data hKr hperf
      (frobOnPlacesGeomLevel_surjective K N data hKr hperf) hD)

end Pic0Ops

section Relation

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
variable (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1)

include data hKr hperf hdeg1 in

end Relation

end ModularCurve

noncomputable section

open AlgebraicCurve Matrix Polynomial ValuationSubring Ideal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

variable (K : Type*) [Field K]

variable (N : ℕ) [NeZero N]
variable [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def frobeniusPushforwardGeomLevelPic0OfIsCurveOver :
    Pic0 K (modularFunctionFieldC K N) →+ Pic0 K (modularFunctionFieldC K N) :=
  frobeniusPushforwardGeomLevelPic0 K N data hKr (perfect_of_isAlgClosed K)
    (deg_eq_one_modularFunctionFieldC K N)

def frobeniusPullbackGeomLevelPic0OfIsCurveOver :
    Pic0 K (modularFunctionFieldC K N) →+ Pic0 K (modularFunctionFieldC K N) :=
  frobeniusPullbackGeomLevelPic0 K N data hKr (perfect_of_isAlgClosed K)
    (deg_eq_one_modularFunctionFieldC K N)

def heckeFibreGeomLevelPic0OfIsCurveOver :
    Pic0 K (modularFunctionFieldC K N) →+ Pic0 K (modularFunctionFieldC K N) :=
  heckeFibreGeomLevelPic0 K N data hKr (perfect_of_isAlgClosed K)
    (deg_eq_one_modularFunctionFieldC K N)

end ModularCurve

namespace ModularCurve
open AlgebraicCurve Matrix Polynomial ValuationSubring Ideal
section FamilyProps

variable (K : Type*) [Field K]

def IsCurveOverModularFunctionFieldCFamily : Prop :=
  ∀ (N : ℕ), [NeZero N] → IsCurveOver K (modularFunctionFieldC K N)

variable (N : ℕ) [NeZero N]
variable [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def SpecialFibreHeckeModuleMatch
    (inst : Module HeckeAlg (Pic0 K (modularFunctionFieldC K N))) : Prop :=
  ∀ x : Pic0 K (modularFunctionFieldC K N),
    letI := inst
    heckeGen ⟨ℓ, hℓ.out⟩ • x = heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr x

end FamilyProps
end ModularCurve

end
end
end
end
end
end
end
