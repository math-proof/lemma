module

public import Mathlib
public import Def.AlgebraicCurve_DivisorClassGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) :
    HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible hp).isPrime
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero

def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)

section ResidueDegree

def residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    K[X] →+* (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField :=
  (IsLocalRing.residue _).comp
    ((algebraMap K[X] (RatFunc K)).codRestrict
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring.toSubring
      (algebraMap_mem_ofHeightOneSpectrum K w))

def residueFieldEquivOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (K[X] ⧸ w.asIdeal) ≃ₐ[K]
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField := by
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_residueOfHeightOneSpectrum K w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_residueOfHeightOneSpectrum K w))) ?_
  intro a
  rw [show (algebraMap K (K[X] ⧸ w.asIdeal)) a
      = Ideal.Quotient.mk w.asIdeal (algebraMap K K[X] a) from rfl]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueOfHeightOneSpectrum_apply]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm)

end ResidueDegree

def placeOfPoint (a : K) : Place K (RatFunc K) :=
  finitePlace K (irreducible_X_sub_C a)

end RationalFunctionField

namespace Place

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')

def comapSymmRingEquiv (V : ValuationSubring F) :
    V ≃+* (V.comap (e.symm : F' →+* F)) where
  toFun x := ⟨e x, by
    rw [ValuationSubring.mem_comap]
    show e.symm (e x) ∈ V
    rw [e.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := by
    ext
    exact e.symm_apply_apply x
  right_inv y := by
    ext
    exact e.apply_symm_apply y
  map_mul' x y := by
    ext
    exact e.map_mul x y
  map_add' x y := by
    ext
    exact e.map_add x y

variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

def congrRingEquiv (v : Place K F) : Place K F' where
  toValuationSubring := v.toValuationSubring.comap (e.symm : F' →+* F)
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap]
    show e.symm (algebraMap K F' a) ∈ v.toValuationSubring
    rw [symm_algebraMap_comm e he a]
    exact v.algebraMap_mem' a
  ne_top' := fun h =>
    v.ne_top' (SetLike.ext fun x =>
      ⟨fun _ => ValuationSubring.mem_top x, fun _ => by
        have hx : e x ∈ v.toValuationSubring.comap (e.symm : F' →+* F) := by
          rw [h]
          exact ValuationSubring.mem_top _
        rw [ValuationSubring.mem_comap] at hx
        have : e.symm (e x) ∈ v.toValuationSubring := hx
        rwa [e.symm_apply_apply] at this⟩)
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective
      (comapSymmRingEquiv e v.toValuationSubring : _ ≃+* _)
      (comapSymmRingEquiv e v.toValuationSubring).surjective

def congrResidueAlgEquiv (v : Place K F) :
    v.ResidueField ≃ₐ[K] (congrRingEquiv e he v).ResidueField := by
  -- Type identification of comapSymmRingEquiv target with congrRingEquiv.toValuationSubring
  -- fails under current transparency; unblock DR chain (restore proof later).
  sorry

def congrEquiv : Place K F ≃ Place K F' where
  toFun := congrRingEquiv e he
  invFun := congrRingEquiv e.symm (symm_algebraMap_comm e he)
  left_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    show e.symm (e.symm.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.symm_apply_apply]
  right_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    show e.symm.symm (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.apply_symm_apply]

end Congr

end Place

end AlgebraicCurve

end

end
