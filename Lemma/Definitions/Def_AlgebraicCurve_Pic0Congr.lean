import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

namespace Divisor

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

def congr : Divisor K F ≃+ Divisor K F' :=
  Finsupp.domCongr (Place.congrEquiv e he)

@[simp]
theorem congr_single (v : Place K F) (n : ℤ) :
    congr e he (Finsupp.single v n) = Finsupp.single (Place.congrRingEquiv e he v) n :=
  Finsupp.equivMapDomain_single (Place.congrEquiv e he) v n

theorem congr_apply_place_congr (D : Divisor K F) (v : Place K F) :
    congr e he D (Place.congrRingEquiv e he v) = D v := by
  show Finsupp.equivMapDomain (Place.congrEquiv e he) D (Place.congrEquiv e he v) = D v
  rw [Finsupp.equivMapDomain_apply]
  exact congrArg D ((Place.congrEquiv e he).symm_apply_apply v)

theorem congr_symm_apply_place (D : Divisor K F') (v : Place K F) :
    (congr e he).symm D v = D (Place.congrRingEquiv e he v) := by
  show Finsupp.equivMapDomain (Place.congrEquiv e he).symm D v = _
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  rfl

@[simp]
theorem degree_congr (D : Divisor K F) : degree (congr e he D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [map_add, map_add, map_add, ih, congr_single, degree_single, degree_single,
        Place.deg_congrRingEquiv]

@[simp]
theorem degree_congr_symm (D : Divisor K F') : degree ((congr e he).symm D) = degree D := by
  conv_rhs => rw [← (congr e he).apply_symm_apply D]
  rw [degree_congr]

theorem congr_mem_degZero {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) : congr e he D ∈ degZero (K := K) (F := F') := by
  rwa [mem_degZero, degree_congr]

theorem congr_symm_mem_degZero {D : Divisor K F'}
    (hD : D ∈ degZero (K := K) (F := F')) :
    (congr e he).symm D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_congr_symm]

theorem congr_mem_principal {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) :
    congr e he D ∈ principal (K := K) (F := F') := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨e f, by simpa using hf, fun w => ?_⟩
  have hw : w = Place.congrRingEquiv e he ((Place.congrEquiv e he).symm w) :=
    ((Place.congrEquiv e he).apply_symm_apply w).symm
  rw [hw, congr_apply_place_congr, hD ((Place.congrEquiv e he).symm w)]
  exact (Place.ord_congrRingEquiv e he ((Place.congrEquiv e he).symm w) f).symm

theorem congr_symm_mem_principal {D : Divisor K F'}
    (hD : D ∈ principal (K := K) (F := F')) :
    (congr e he).symm D ∈ principal (K := K) (F := F) := by
  obtain ⟨f', hf', hD⟩ := hD
  refine ⟨e.symm f', by simpa using hf', fun v => ?_⟩
  rw [congr_symm_apply_place, hD (Place.congrRingEquiv e he v)]
  have h := Place.ord_congrRingEquiv e he v (e.symm f')
  rwa [e.apply_symm_apply] at h

end Divisor

namespace Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

def degZeroCongr :
    Divisor.degZero (K := K) (F := F) ≃+ Divisor.degZero (K := K) (F := F') where
  toFun D := ⟨Divisor.congr e he D, Divisor.congr_mem_degZero e he D.2⟩
  invFun D := ⟨(Divisor.congr e he).symm D, Divisor.congr_symm_mem_degZero e he D.2⟩
  left_inv D := Subtype.ext ((Divisor.congr e he).symm_apply_apply D)
  right_inv D := Subtype.ext ((Divisor.congr e he).apply_symm_apply D)
  map_add' D E := Subtype.ext (map_add (Divisor.congr e he) (D : Divisor K F) (E : Divisor K F))

@[simp]
theorem coe_degZeroCongr (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroCongr e he D : Divisor K F') = Divisor.congr e he (D : Divisor K F) := rfl

@[simp]
theorem coe_degZeroCongr_symm (D : Divisor.degZero (K := K) (F := F')) :
    ((degZeroCongr e he).symm D : Divisor K F)
      = (Divisor.congr e he).symm (D : Divisor K F') := rfl

theorem map_principal_degZeroCongr :
    ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))).map (degZeroCongr e he).toAddMonoidHom
      = (Divisor.principal (K := K) (F := F')).addSubgroupOf
          (Divisor.degZero (K := K) (F := F')) := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddEquiv.coe_toAddMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Divisor.congr_mem_principal e he hx
  · intro hy
    refine ⟨(degZeroCongr e he).symm y, ?_, (degZeroCongr e he).apply_symm_apply y⟩
    rw [coe_degZeroCongr_symm]
    exact Divisor.congr_symm_mem_principal e he hy

def congr : Pic0 K F ≃+ Pic0 K F' :=
  QuotientAddGroup.congr _ _ (degZeroCongr e he) (map_principal_degZeroCongr e he)

end Pic0

end AlgebraicCurve
