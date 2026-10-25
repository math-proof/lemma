import Instance.LanglandsTunnell_ArtinFrobenius
import Def.M4aHerbrand_IdeleClassVocab
import Instance.LanglandsTunnell_ArtinCoreCTM
import Structure.LanglandsTunnell_ArtinCoreCTM

set_option autoImplicit false

noncomputable section

open Deep.NTSupply NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace HeckeCharacter

section RelNorm

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]


end RelNorm

section Content

variable (K : Type*) [Field K] [NumberField K]

theorem fad_one_apply (v : HeightOneSpectrum (𝓞 K)) :
    ((1 : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = 1 := rfl

theorem fad_mul_apply (a b : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ((a * b : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = a v * b v := rfl

def placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -WithZero.log (Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))

theorem placeOrd_one (v : HeightOneSpectrum (𝓞 K)) : placeOrd K 1 v = 0 := by
  unfold placeOrd
  rw [Units.val_one, fad_one_apply, map_one, WithZero.log_one, neg_zero]

theorem valued_ne_zero_of_unit (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  exact ((FiniteAdeleRing.isUnit_iff.mp u.isUnit).1 v)

theorem placeOrd_mul (u u' : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (u * u') v = placeOrd K u v + placeOrd K u' v := by
  unfold placeOrd
  rw [Units.val_mul, fad_mul_apply, map_mul,
    WithZero.log_mul (valued_ne_zero_of_unit K u v) (valued_ne_zero_of_unit K u' v),
    neg_add]

theorem placeOrd_eq_zero_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K u v = 0 ↔ Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  unfold placeOrd
  rw [neg_eq_zero]
  constructor
  · intro hlog
    have h := WithZero.exp_log (x := Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))
      (valued_ne_zero_of_unit K u v)
    rw [hlog, WithZero.exp_zero] at h
    exact h.symm
  · intro h; rw [h, WithZero.log_one]

theorem finite_support_placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.support (placeOrd K u)).Finite := by
  have h := FiniteAdeleRing.unitsEquiv_finite_valued_eq_one (R := 𝓞 K) (K := K) u
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  rw [Function.mem_support] at hv
  rw [Set.mem_setOf_eq]
  intro hval
  exact hv ((placeOrd_eq_zero_iff K u v).mpr (by
    set_option backward.isDefEq.respectTransparency false in
    simpa [RestrictedProduct.unitsEquiv_apply] using hval))

def fadContentHom : (FiniteAdeleRing (𝓞 K) K)ˣ →* (FractionalIdeal ((𝓞 K)⁰) K)ˣ where
  toFun u := ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v)
  map_one' := by simp [placeOrd_one]
  map_mul' u u' := by
    simp only [placeOrd_mul, zpow_add]
    exact finprod_mul_distrib
      ((finite_support_placeOrd K u).subset fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
        contrapose! hv; rw [Function.mem_support, not_not] at hv; simp [hv])
      ((finite_support_placeOrd K u').subset fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
        contrapose! hv; rw [Function.mem_support, not_not] at hv; simp [hv])

def projFin : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd (InfiniteAdeleRing K)ˣ (FiniteAdeleRing (𝓞 K) K)ˣ).comp
    MulEquiv.prodUnits.toMonoidHom


open InfinitePlace.Completion in


open InfinitePlace.Completion in
theorem archRealProjTau_mul (τ : K →+* ℝ) (u u' : (AdeleRing (𝓞 K) K)ˣ) :
    archRealProjTau K τ (u * u') = archRealProjTau K τ u * archRealProjTau K τ u' := by
  unfold archRealProjTau
  rw [← map_mul]; rfl

open InfinitePlace.Completion in
theorem archRealProjTau_ne_zero (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archRealProjTau K τ u ≠ 0 := by
  intro h
  have h1 : archRealProjTau K τ u * archRealProjTau K τ u⁻¹ = 1 := by
    rw [← archRealProjTau_mul, mul_inv_cancel]
    unfold archRealProjTau; rw [Units.val_one]
    exact (congrArg (ringEquivRealOfIsReal (isReal_placeOf K τ)) rfl).trans (map_one _)
  rw [h, zero_mul] at h1; exact zero_ne_one h1


open InfinitePlace.Completion in

theorem archSign_of_fst_eq_one (τ : K →+* ℝ) {u : (AdeleRing (𝓞 K) K)ˣ}
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1) : archSign K τ u := by
  show (0:ℝ) < ringEquivRealOfIsReal (isReal_placeOf K τ) _
  rw [huarch, show ((1 : InfiniteAdeleRing K) (placeOf K τ)) = 1 from rfl, map_one]
  exact one_pos

theorem archSign_mul (τ : K →+* ℝ) (u u' : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ (u * u') ↔ (archSign K τ u ↔ archSign K τ u') := by
  unfold archSign; rw [archRealProjTau_mul]
  constructor
  · intro hmul
    rcases mul_pos_iff.mp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact iff_of_true h1 h2
    · exact iff_of_false h1.not_gt h2.not_gt
  · intro hiff
    rcases (archRealProjTau_ne_zero K τ u).lt_or_gt with h1 | h1
    · have h2 := (not_iff_not.mpr hiff).mp h1.not_gt
      exact mul_pos_of_neg_of_neg h1 ((archRealProjTau_ne_zero K τ u').lt_or_gt.resolve_right h2)
    · exact mul_pos h1 (hiff.mp h1)

theorem archSign_one (τ : K →+* ℝ) : archSign K τ 1 :=
  archSign_of_fst_eq_one K τ rfl

theorem archSign_inv (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ u⁻¹ ↔ archSign K τ u := by
  have h := archSign_mul K τ u u⁻¹
  rw [mul_inv_cancel, iff_true_intro (archSign_one K τ), true_iff] at h
  exact h.symm

theorem unit_cong_mul {v : HeightOneSpectrum (𝓞 K)} {ε : ℤᵐ⁰} {a b : v.adicCompletion K}
    (hva : Valued.v a = 1) (hca : Valued.v (a - 1) ≤ ε)
    (hvb : Valued.v b = 1) (hcb : Valued.v (b - 1) ≤ ε) :
    Valued.v (a * b) = 1 ∧ Valued.v (a * b - 1) ≤ ε := by
  refine ⟨by rw [map_mul, hva, hvb, one_mul], ?_⟩
  have heq : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  calc Valued.v (a * b - 1) = Valued.v (a * (b - 1) + (a - 1)) := by rw [heq]
    _ ≤ max (Valued.v (a * (b - 1))) (Valued.v (a - 1)) := Valuation.map_add _ _ _
    _ ≤ ε := by
        rw [map_mul, hva, one_mul]
        exact max_le hcb hca

theorem unit_cong_div {v : HeightOneSpectrum (𝓞 K)} {ε : ℤᵐ⁰} {a b : v.adicCompletion K}
    (hca : Valued.v (a - 1) ≤ ε)
    (hvb : Valued.v b = 1) (hcb : Valued.v (b - 1) ≤ ε) :
    Valued.v (a * b⁻¹ - 1) ≤ ε := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hvb
  have heq : a * b⁻¹ - 1 = (a - b) * b⁻¹ := by field_simp
  rw [heq, map_mul, map_inv₀, hvb, inv_one, mul_one]
  calc Valued.v (a - b) = Valued.v ((a - 1) - (b - 1)) := by ring_nf
    _ ≤ max (Valued.v (a - 1)) (Valued.v (b - 1)) := Valuation.map_sub _ _ _
    _ ≤ ε := max_le hca hcb

theorem fad_units_inv_apply (X : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (((X⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)
      = (((X : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← fad_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, fad_one_apply]


end Content

end HeckeCharacter

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter WithZero

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))


end Carriers

section Inclusion

variable (K : Type*) [Field K] [NumberField K]


end Inclusion

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N]
  [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]


end Tower

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]


end Admissible

section DefN

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def normRaySubgroup (𝔣 : Ideal (𝓞 K)) : Subgroup ↥(coprimeToModulus K 𝔣) :=
  (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣)
    ⊔ (HeckeCharacter.relNormCTM K L 𝔣).range

end DefN

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def SecondInequalityCTM (𝔣 : Ideal (𝓞 K)) : Prop :=
  (normRaySubgroup K L 𝔣).index ∣ Nat.card (L ≃ₐ[K] L)

def FirstInequalityCTM (𝔣 : Ideal (𝓞 K)) : Prop :=
  Nat.card (L ≃ₐ[K] L) ∣ (normRaySubgroup K L 𝔣).index

end Pincer

section UnitIdeles

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

def unitIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ where
  carrier := {u | (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ τ : K →+* ℝ, archSign K τ u}
  one_mem' := ⟨fun v => by rw [map_one, Units.val_one, fad_one_apply, map_one],
    fun v _ => by rw [map_one, Units.val_one, fad_one_apply, sub_self, map_zero]; exact zero_le', fun τ => archSign_one K τ⟩
  mul_mem' {u u'} hu hu' := by
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => (archSign_mul K τ u u').mpr (iff_of_true (hu.2.2 τ) (hu'.2.2 τ))⟩
    · rw [map_mul, Units.val_mul, fad_mul_apply, map_mul, hu.1 v, hu'.1 v, one_mul]
    · rw [map_mul, Units.val_mul, fad_mul_apply]
      exact (unit_cong_mul K (hu.1 v) (hu.2.1 v hv) (hu'.1 v) (hu'.2.1 v hv)).2
  inv_mem' {u} hu := by
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => (archSign_inv K τ u).mpr (hu.2.2 τ)⟩
    · rw [map_inv, fad_units_inv_apply, map_inv₀, hu.1 v, inv_one]
    · rw [map_inv, fad_units_inv_apply]
      have h := unit_cong_div K (a := (1 : v.adicCompletion K)) (by rw [sub_self, map_zero]; exact zero_le') (hu.1 v) (hu.2.1 v hv)
      rwa [one_mul] at h

end UnitIdeles


section PerICore

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
  (c : ArtinFieldCore K L 𝔣 i)


def ArtinFieldCore.Ni : c.Ip →* ↥(coprimeToModulus K 𝔣) :=
  (ctmInclusion K c.h𝔪).comp (relNormCTM K c.E c.𝔪)


def ArtinFieldCore.Pi : c.Ip := ⟨primeUnit c.E c.w, primeUnit_mem_coprimeToModulus c.E c.hw⟩

end PerICore


section IdeleData

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]

def IdeleFirstIneqData (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∃ Nrm : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 K) K)ˣ,
    (∀ {u : (AdeleRing (𝓞 F) F)ˣ} {α : (F)ˣ},
      IsAdjuster F (modulusExt K F 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α)) ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K F (fadContentHom F (projFin F u))) ∧
    (IsAdmissibleModulus K F 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range) ∧
    Module.finrank K F ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index

end IdeleData

section IdeleDataTop

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def IdeleFirstIneqDataAt (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∃ Nrm : (AdeleRing (𝓞 M) M)ˣ →* (AdeleRing (𝓞 K) K)ˣ,
    (∀ {u : (AdeleRing (𝓞 M) M)ˣ} {α : Mˣ},
      IsAdjuster M (modulusExt K M 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α)) ∧
    (∀ u : (AdeleRing (𝓞 M) M)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K M (fadContentHom M (projFin M u))) ∧
    (IsAdmissibleModulus K M 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range) ∧
    Module.finrank K M ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index

end IdeleDataTop

end LanglandsTunnell.P2.Artin
