module
public import Theorem.HahnSeries.JqCoeff
public import Theorem.LaurentSeries.LaurentCoeff
public import Def.ModularCurve_PhiGen
public import Class.AlgebraicCurve_DivisorClassGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Algebraic.Basic
public import Def.AlgebraicCurve_PlacesOverDVR
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Int.CharZero
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Def.ModularCurve_FibreModel
public import Def.ModularCurve_ArithmeticGalois
public import Structure.ModularCurve_PlaceSpecialization
public import Instance.ModularCurve_SpecializationMap
set_option autoImplicit false


public section

noncomputable section


set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace CharPModel

section LaurentMap

variable {R S : Type*} [CommRing R] [CommRing S]

private def laurentMapRingHom (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one, apply_ite f,
      map_one, map_zero]
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_zero, HahnSeries.coeff_zero, map_zero]
  map_add' x y := HahnSeries.map_add f.toAddMonoidHom

end LaurentMap


end CharPModel
end ModularCurve

noncomputable section

namespace ModularCurve
namespace CharPModel

section LineTier

section ResidueFieldInline

variable {K₀ F₀ F₀' : Type*} [Field K₀] [Field F₀] [Field F₀'] [Algebra K₀ F₀] [Algebra K₀ F₀']
  [Algebra F₀ F₀'] [IsScalarTower K₀ F₀ F₀'] [FiniteDimensional F₀ F₀']

end ResidueFieldInline

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
private def jLine (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    modularFunctionFieldC k N := ⟨jqModC k, jqModC_mem k N⟩

set_option synthInstance.maxHeartbeats 400000 in
private def jNLine (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    modularFunctionFieldC k N := ⟨jqNModC k N, jqNModC_mem k N⟩

set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def lineEquivC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    RatFunc k ≃ₐ[k]
      (IntermediateField.adjoin k
        ({jLine k N} : Set (modularFunctionFieldC k N))) :=
  RatFunc.algEquivOfTranscendental _ (transcendental_jLine k N)

end LineTier

section BarFinDim

private def jdBar (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) :
    laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
private def barGenSet (N : ℕ) [NeZero N] :
    Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  Subtype.val ⁻¹' (⇑(coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions N)

end BarFinDim

end CharPModel
end ModularCurve

set_option autoImplicit false

open Polynomial

namespace ValuationSubring

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)

private noncomputable def polynomialEquivClosure {x : F} (hx : Transcendental K x) :
    A[X] ≃+* Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) :=
  RingEquiv.ofBijective
    ((aeval (R := A) x).toRingHom.codRestrict _ (A.aeval_mem_closure x))
    ⟨fun p q h => A.aeval_injective_of_transcendental hx (Subtype.ext_iff.mp h),
      fun y => by
        obtain ⟨p, hp⟩ : (y : F) ∈ (aeval (R := A) x).toRingHom.range := by
          rw [← closureConstantsAdjoin_eq_range_aeval]
          exact y.2
        exact ⟨p, Subtype.ext hp⟩⟩

end ValuationSubring


set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private def HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

variable (A : ValuationSubring K)

private def compSubring : Subring F where
  carrier := {f | ∃ a : A, w.HasValueAt f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simpa using ha.mul hb⟩
  one_mem' := ⟨1, by simpa using w.hasValueAt_algebraMap 1⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using w.hasValueAt_algebraMap 0⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, by simpa using ha.neg⟩

variable {A} in
variable {A} in
private def value : w.compSubring A →+* A where
  toFun f := Classical.choose f.2
  map_one' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).one_mem).unique (by
      simpa using w.hasValueAt_algebraMap 1)
  map_mul' f g := Subtype.ext <|
    (Classical.choose_spec (mul_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).mul (Classical.choose_spec g.2))
  map_zero' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).zero_mem).unique (by
      simpa using w.hasValueAt_algebraMap 0)
  map_add' f g := Subtype.ext <|
    (Classical.choose_spec (add_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).add (Classical.choose_spec g.2))

variable {A} in
variable {A} in
variable {A} in
variable {A} in
private def centre : Ideal (w.compSubring A) := (maximalIdeal A).comap (w.value A)

variable {A} in
variable {A} in
variable {A} in
variable {A} in
variable {A} in
private def compValuationSubring (hw : Function.Surjective (algebraMap K w.ResidueField)) :
    ValuationSubring F :=
  ValuationSubring.ofSubring (w.compSubring A) (w.mem_compSubring_or_inv_mem A hw)

end Place

end AlgebraicCurve

set_option autoImplicit false

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

section Quotient

open Polynomial

variable {F : Type*} [Field F] [Algebra K F]

private abbrev constants : A →+* F := (algebraMap K F).comp A.subtype

variable {A}

end Quotient

end ValuationSubring

set_option autoImplicit false

noncomputable section

open IsLocalRing IsDedekindDomain


namespace ValuationSubring

variable {F : Type*} [Field F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (O : ValuationSubring F)

private def centreOver (hO : ∀ r : R, algebraMap R F r ∈ O) : Ideal R :=
  (IsLocalRing.maximalIdeal O).comap ((algebraMap R F).codRestrict O.toSubring hO)

omit [IsDedekindDomain R] [IsFractionRing R F] in
private def centreHeightOneSpectrum (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    HeightOneSpectrum R :=
  ⟨O.centreOver hO, inferInstance, O.centreOver_ne_bot hO hne⟩

end ValuationSubring

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

private def ofValuationSubringOver (O : ValuationSubring F) (hO : ∀ r : R, algebraMap R F r ∈ O)
    (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O) : Place K F where
  toValuationSubring := O
  algebraMap_mem' := hK
  ne_top' := hne
  isPrincipalIdealRing' := O.isPrincipalIdealRing_of_dedekind_le hO hne

end Place

end AlgebraicCurve

set_option autoImplicit false

open IsLocalRing Polynomial


set_option autoImplicit false

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial


set_option autoImplicit false

open Polynomial


set_option autoImplicit false

namespace RingHom

variable {B C : Type*} [CommRing B] [CommRing C] (π : B →+* C)

private def imagePrime (𝔮 : Ideal B) : Ideal π.range := 𝔮.map π.rangeRestrict

end RingHom


namespace ModularCurve
namespace CharPModel

open AlgebraicCurve AlgebraicCurve.Place Ideal

section SpecializationConstruction

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def FibreModel.centreFin (fm : FibreModel N A ℓ k red)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hwFin : (jBar N : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) ∈ w.compSubring A) : Ideal fm.BFin :=
  (w.centre A).comap (Subring.inclusion (fm.bfin_le_compSubring w hwFin))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def lineClosure (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Subalgebra (Algebra.adjoin k ({jLine k N} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) :=
  integralClosure (Algebra.adjoin k ({jLine k N} : Set (modularFunctionFieldC k N)))
    (modularFunctionFieldC k N)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def FibreModel.centreInf (fm : FibreModel N A ℓ k red)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hwInf : ((jBar N)⁻¹ : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) ∈ w.compSubring A) : Ideal fm.BInf :=
  (w.centre A).comap (Subring.inclusion (fm.binf_le_compSubring w hwInf))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def lineClosureInf (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Subalgebra (Algebra.adjoin k (({(jLine k N)⁻¹} : Set (modularFunctionFieldC k N))))
      (modularFunctionFieldC k N) :=
  integralClosure (Algebra.adjoin k (({(jLine k N)⁻¹} : Set (modularFunctionFieldC k N))))
    (modularFunctionFieldC k N)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
open Classical in
private noncomputable def FibreModel.sp (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) →
    Place k (modularFunctionFieldC k N) :=
  fun w =>
    if h : (jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) ∈ w.compSubring A then
      (fm.exists_spFin hred (dataAll N (dvd_refl N)) hsep w h).choose
    else
      (fm.exists_spInf hred (dataAll N (dvd_refl N)) hsep w
        ((fm.chart_dichotomy dataAll w).resolve_left h)).choose

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable def FibreModel.spPlace (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) → Place k (modularFunctionFieldC k N) :=
  fm.sp hred dataAll hsep

noncomputable def FibreModel.spDiv (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Divisor k (modularFunctionFieldC k N) :=
  Finsupp.mapDomain (fm.spPlace hred dataAll hsep)

def FibreModel.SpDivPreservesPrincipal (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) : Prop :=
  (∀ D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N),
      fm.spDiv hred dataAll hsep D ∈
        Divisor.degZero (K := k) (F := modularFunctionFieldC k N)) ∧
  (∀ D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N),
      D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) →
      fm.spDiv hred dataAll hsep D ∈
        Divisor.principal (K := k) (F := modularFunctionFieldC k N))

open Classical in

noncomputable def FibreModel.spPic0 (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    JZero N →+ Pic0 k (modularFunctionFieldC k N) :=
  if h : fm.SpDivPreservesPrincipal hred dataAll hsep then
    QuotientAddGroup.map _ _
      (AddMonoidHom.mk'
        (fun D => ⟨fm.spDiv hred dataAll hsep ↑D, h.1 ↑D D.2⟩)
        (fun D E => Subtype.ext (by
          show fm.spDiv hred dataAll hsep ↑(D + E)
              = fm.spDiv hred dataAll hsep ↑D + fm.spDiv hred dataAll hsep ↑E
          rw [AddSubgroup.coe_add]
          exact Finsupp.mapDomain_add)))
      (fun D hD => AddSubgroup.mem_comap.mpr ((AddSubgroup.mem_addSubgroupOf).mpr
        (h.2 ↑D D.2 ((AddSubgroup.mem_addSubgroupOf).mp hD))))
  else 0

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

noncomputable def FibreModel.placeSpecializationOf (fm : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (h_d0_j : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) (red a)))
    (h_d0_j_pole : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    ((fm.spPlace hred dataAll hsep) w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        < 0)
    (h_d0_jN : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩
          - algebraMap k (modularFunctionFieldC k N) (red a)))
    (h_d0_jN_pole : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    ((fm.spPlace hred dataAll hsep) w).ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k
        N) < 0)
    (h_d1 : ∀ W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
    (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)
        = frobOnPlacesGeomLevel k N data hKr
            ((fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
                hβ))
      ∨ frobOnPlacesGeomLevel k N data hKr
            ((fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N
                ℓ) hα))
        = (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
            hβ))
    (h_d2 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v)) ≠ (fm.spPlace hred
            dataAll hsep) v →
    ∃ W₀ : Place (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
      W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v
        ∧ (fm.spPlace hred dataAll hsep) (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
            hα)
            = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v)
        ∧ W₀.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) = 1
        ∧ ∀ W : Place (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
            W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v →
            (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
                hα)
                = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v) →
              W = W₀)
    (h_d4 : Function.Surjective (fm.spPlace hred dataAll hsep))
    (h_d5 : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, D v = v.ord f) →
      ∃ g : modularFunctionFieldC k N, g ≠ 0 ∧
        ∀ v' : Place k (modularFunctionFieldC k N),
          Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D v' = v'.ord g)
    (h_d6_inertia : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w) =
          (fm.spPlace hred dataAll hsep) w)
    (h_d6_frobenius : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    A.IsFrobeniusAt σ ℓ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w)
        = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) w))
    (h_d7_dictInfty : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)))
    (h_d7_dictZero : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)))
    (h_spPic0_compat :
    ∀ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)),
      ∃ D' : Divisor.degZero (K := k) (F := ↥(modularFunctionFieldC k N)),
        (D' : Divisor k (modularFunctionFieldC k N))
            = Finsupp.mapDomain (fm.spPlace hred dataAll hsep)
                (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
          ∧ (fm.spPic0 hred dataAll hsep) (Pic0.mk D) = Pic0.mk D')
    : PlaceSpecialization A ℓ N data hKr k red hα hβ :=
  ⟨fm.spPlace hred dataAll hsep, fm.spPic0 hred dataAll hsep, h_d0_j, h_d0_j_pole, h_d0_jN,
      h_d0_jN_pole, h_d1, h_d2, h_d4, h_d5, h_d6_inertia, h_d6_frobenius, h_d7_dictInfty,
      h_d7_dictZero, h_spPic0_compat⟩

end SpecializationConstruction

end CharPModel
end ModularCurve

end
end
end
end
end
end
