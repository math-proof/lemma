import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Chapter3.DedekindProperties.Part2
open Ideal nonZeroDivisors DedekindDomainEquiv FractionalIdealLocalization
open nonZeroDivisors


namespace DedekindDomainEquiv

/--
[integrallyClosed_iff_dvrLocalizations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_iff_dvrLocalizations
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  CondIntegrallyClosed A ↔ CondDvrLocalizations A := by
-- proof
  unfold CondIntegrallyClosed CondDvrLocalizations
  constructor
  · intro h; exact @IsDedekindDomain.isDedekindDomainDvr A _ _ h
  · intro h; exact @IsDedekindDomainDvr.isDedekindDomain A _ _ h

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[integrallyClosed_iff_invertibleIdeals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_iff_invertibleIdeals
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  CondIntegrallyClosed A ↔ CondInvertibleIdeals A := by
-- proof
  unfold CondIntegrallyClosed CondInvertibleIdeals
  exact isDedekindDomain_iff_isDedekindDomainInv

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[integrallyClosed_to_primeFactorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_to_primeFactorization
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h : CondIntegrallyClosed A) :
-- imply
  CondPrimeFactorization A := by
-- proof
  unfold CondIntegrallyClosed at h; unfold CondPrimeFactorization
  intro I hI
  haveI := h
  obtain ⟨f, hf_prime, hf_assoc⟩ := UniqueFactorizationMonoid.exists_prime_factors I hI
  exact ⟨f, hf_prime, associated_iff_eq.mp hf_assoc⟩

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[integrallyClosed_to_containIsDivide](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_to_containIsDivide
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h : CondIntegrallyClosed A) :
-- imply
  CondContainIsDivide A := by
-- proof
  unfold CondIntegrallyClosed at h; unfold CondContainIsDivide
  haveI := h
  exact ⟨inferInstance, fun I J => Ideal.dvd_iff_le⟩

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[containIsDivide_to_integrallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma containIsDivide_to_integrallyClosed
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  CondContainIsDivide A → CondIntegrallyClosed A := by
-- proof
  unfold CondContainIsDivide CondIntegrallyClosed
  intro ⟨hnoeth, hdvd⟩
  haveI := hnoeth
  apply IsDedekindDomainInv.isDedekindDomain
  intro I hI
  obtain ⟨a, J, ha, rfl⟩ := exists_eq_spanSingleton_mul I
  have ha_map : (algebraMap A (FractionRing A) a)⁻¹ ≠ 0 := by simp [ha]
  have hspan_unit : IsUnit (spanSingleton A⁰ (algebraMap A (FractionRing A) a)⁻¹) :=
    (mul_inv_cancel_iff_isUnit (FractionRing A)).mp
      (spanSingleton_mul_inv (FractionRing A) ha_map)
  have hJ : J ≠ ⊥ := by
    intro heq; apply hI; simp [heq, FractionalIdeal.bot_eq_zero]
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hle : Ideal.span {x} ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxJ)
  obtain ⟨K, hK⟩ := (hdvd J (Ideal.span {x})).mpr hle
  have hfrac : (↑J : FractionalIdeal A⁰ (FractionRing A)) * ↑K = ↑(Ideal.span {x}) := by
    rw [← coeIdeal_mul, hK]
  have hinv : (↑(Ideal.span {x}) : FractionalIdeal A⁰ (FractionRing A)) *
    (↑(Ideal.span {x}))⁻¹ = 1 :=
    coe_ideal_span_singleton_mul_inv (FractionRing A) hx0
  have hJ_unit : IsUnit (↑J : FractionalIdeal A⁰ (FractionRing A)) :=
    (mul_inv_cancel_iff_isUnit (FractionRing A)).mp
      ((mul_inv_cancel_iff (FractionRing A)).mpr
        ⟨↑K * (↑(Ideal.span {x}))⁻¹, by rw [← mul_assoc, hfrac, hinv]⟩)
  exact (mul_inv_cancel_iff_isUnit (FractionRing A)).mpr (IsUnit.mul hspan_unit hJ_unit)

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[integrallyClosed_to_principalProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_to_principalProduct
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h : CondIntegrallyClosed A) :
-- imply
  CondPrincipalProduct A := by
-- proof
  unfold CondIntegrallyClosed at h; unfold CondPrincipalProduct
  haveI := h
  intro I hI
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha_le : Ideal.span {a} ≤ I := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haI)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ha_le
  refine ⟨J, hJ ▸ ⟨⟨a, rfl⟩⟩, ?_⟩
  rw [← hJ]
  rwa [Ne, Ideal.span_singleton_eq_bot]

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[principalProduct_to_integrallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma principalProduct_to_integrallyClosed
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  CondPrincipalProduct A → CondIntegrallyClosed A := by
-- proof
  unfold CondPrincipalProduct CondIntegrallyClosed
  intro h6
  apply IsDedekindDomainInv.isDedekindDomain
  rw [isDedekindDomainInv_iff (K := FractionRing A)]
  intro I hI
  obtain ⟨a, aI, ha, hI_eq⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haI : aI ≠ ⊥ := FractionalIdeal.ideal_factor_ne_zero hI hI_eq
  obtain ⟨J, hIJ_princ, hIJ_ne⟩ := h6 aI haI
  obtain ⟨⟨c, hc⟩⟩ := hIJ_princ
  have hc' : aI * J = Ideal.span {c} := by rw [hc]; rfl
  have hc0 : c ≠ 0 := by intro h; apply hIJ_ne; rw [hc', h]; simp
  have h_inv := FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing A) hc0
  have hcoe : (↑(aI * J) : FractionalIdeal A⁰ (FractionRing A)) =
    ↑(Ideal.span {c}) := by exact_mod_cast congrArg _ hc'
  rw [FractionalIdeal.coeIdeal_mul] at hcoe
  rw [← hcoe] at h_inv
  have haIJ_unit : IsUnit (↑aI * ↑J : FractionalIdeal A⁰ (FractionRing A)) :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mp h_inv
  have haI_unit : IsUnit (↑aI : FractionalIdeal A⁰ (FractionRing A)) :=
    isUnit_of_mul_isUnit_left haIJ_unit
  have ha_inv_ne : ((algebraMap A (FractionRing A)) a)⁻¹ ≠ 0 := by simp [ha]
  have hspan_unit : IsUnit (FractionalIdeal.spanSingleton A⁰
    ((algebraMap A (FractionRing A)) a)⁻¹) :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mp
      (FractionalIdeal.spanSingleton_mul_inv (FractionRing A) ha_inv_ne)
  rw [hI_eq]
  exact (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)).mpr
    (hspan_unit.mul haI_unit)

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[integrallyClosed_to_quotientPIR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_to_quotientPIR
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h : CondIntegrallyClosed A) :
-- imply
  CondQuotientPIR A := by
-- proof
  unfold CondIntegrallyClosed at h; unfold CondQuotientPIR
  haveI := h
  intro I hI
  constructor
  intro J
  rw [← map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J]
  set J' := comap (Ideal.Quotient.mk I) J
  have hIJ' : I ≤ J' := by
    intro x hx
    show (Ideal.Quotient.mk I) x ∈ J
    rwa [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_eq_span_pair (hIJ' haI) ha0
  rw [hb, Ideal.map_span, Set.image_pair,
    Ideal.Quotient.eq_zero_iff_mem.mpr haI, Ideal.span_insert_zero]
  exact ⟨⟨(Ideal.Quotient.mk I) b, rfl⟩⟩

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[quotientPIR_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma quotientPIR_noetherian
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h7 : CondQuotientPIR A) :
-- imply
  IsNoetherianRing A := by
-- proof
  unfold CondQuotientPIR at h7
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases hI : I = ⊥
  · subst hI; exact Submodule.fg_bot
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  haveI : IsPrincipalIdealRing (A ⧸ Ideal.span {a}) :=
    h7 (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_bot])
  set f := Ideal.Quotient.mk (Ideal.span ({a} : Set A)) with hf_def
  obtain ⟨⟨b_bar, hb_bar⟩⟩ := IsPrincipalIdealRing.principal (I.map f)
  obtain ⟨b, hb_eq⟩ := Ideal.Quotient.mk_surjective b_bar
  rw [← hb_eq] at hb_bar
  have hle : I ≤ Ideal.span {a, b} := by
    intro x hx
    have hfx : f x ∈ I.map f := Ideal.mem_map_of_mem _ hx
    rw [hb_bar, Submodule.mem_span_singleton] at hfx
    obtain ⟨r_bar, hr⟩ := hfx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r_bar
    have hker : x - r * b ∈ Ideal.span ({a} : Set A) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 : f (x - r * b) = f x - f (r * b) := map_sub f x (r * b)
      have h2 : f (r * b) = f r * f b := map_mul f r b
      have h3 : f r * f b = f r • f b := (smul_eq_mul (f r) (f b)).symm
      rw [h1, h2, h3, hr, sub_self]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hker
    rw [Ideal.mem_span_pair]
    exact ⟨s, r, by rw [show x = (x - r * b) + r * b from by ring, hs, mul_comm a s]⟩
  have hbI : b ∈ I := by
    have hfb : f b ∈ I.map f := by
      rw [hb_bar]; exact Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨y, hyI, hy⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hfb
    have hsub : y - b ∈ Ideal.span ({a} : Set A) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hy, sub_self]
    have hba : b = y - (y - b) := by ring
    rw [hba]
    exact I.sub_mem hyI (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haI) hsub)
  have hge : Ideal.span {a, b} ≤ I := by
    apply Ideal.span_le.mpr
    intro x hx
    cases Set.mem_insert_iff.mp hx with
    | inl h => exact h ▸ haI
    | inr h => exact (Set.mem_singleton_iff.mp h) ▸ hbI
  have hI_eq : I = Ideal.span {a, b} := le_antisymm hle hge
  rw [hI_eq]
  exact Submodule.fg_span (Set.toFinite {a, b})

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[quotientPIR_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma quotientPIR_dvr
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {P : Ideal A}
-- given
  (h7 : CondQuotientPIR A)
  (hPne : P ≠ ⊥)
  (hPpr : P.IsPrime) :
-- imply
  IsDiscreteValuationRing (Localization.AtPrime P) := by
-- proof
  haveI := hPpr
  haveI := quotientPIR_noetherian A h7
  unfold CondQuotientPIR at h7
  set L := Localization.AtPrime P
  set ι := algebraMap A L
  set m := IsLocalRing.maximalIdeal L
  have hP2 : P ^ 2 ≠ ⊥ := by
    intro h; apply hPne; rw [eq_bot_iff]; intro x hx
    have : x ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this; simp only [Ideal.mem_bot, sq_eq_zero_iff] at this; simp [this]
  haveI : IsPrincipalIdealRing (A ⧸ P ^ 2) := h7 _ hP2
  obtain ⟨⟨g, hg⟩⟩ := IsPrincipalIdealRing.principal (Ideal.map (Ideal.Quotient.mk (P ^ 2)) P)
  obtain ⟨π, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hπP : π ∈ P := by
    have hmem : Ideal.Quotient.mk (P ^ 2) π ∈ Ideal.map (Ideal.Quotient.mk (P ^ 2)) P := by
      rw [hg]; exact Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨p, hp, heq⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmem
    rw [show π = p + (π - p) by ring]
    exact P.add_mem hp (Ideal.pow_le_self (n := 2) (by omega) (Ideal.Quotient.eq.mp heq.symm))
  have hPle : P ≤ Ideal.span {π} ⊔ P ^ 2 := by
    intro p hp
    have hmem : Ideal.Quotient.mk (P ^ 2) p ∈ Ideal.map (Ideal.Quotient.mk (P ^ 2)) P :=
      Ideal.mem_map_of_mem _ hp
    rw [hg, Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hr
    have hr' : p - r' * π ∈ P ^ 2 := by have := (P ^ 2).neg_mem hr; rwa [neg_sub] at this
    rw [Submodule.mem_sup]
    exact ⟨r' * π, Ideal.mem_span_singleton.mpr ⟨r', mul_comm r' π⟩, p - r' * π, hr', by ring⟩
  have hm_eq : m = Ideal.map ι P := (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hm_le_sup : m ≤ Ideal.span {ι π} ⊔ m ^ 2 := by
    rw [hm_eq]
    calc Ideal.map ι P
      ≤ Ideal.map ι (Ideal.span {π} ⊔ P ^ 2) := Ideal.map_mono hPle
      _ = Ideal.map ι (Ideal.span {π}) ⊔ Ideal.map ι (P ^ 2) := Ideal.map_sup ι _ _
      _ = Ideal.span {ι π} ⊔ Ideal.map ι (P ^ 2) := by rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {ι π} ⊔ (Ideal.map ι P) ^ 2 := by rw [Ideal.map_pow]
  have hnotfield : ¬IsField L := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    intro h
    exact hPne (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors) |>.mp h)
  have hm_le : m ≤ Ideal.span {ι π} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (N := Ideal.span {ι π}) (N' := m) (I := m)
      (IsNoetherian.noetherian m)
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal L) bot_ne_top])
      (by rwa [Ideal.smul_eq_mul, ← sq])
  have hm_ge : Ideal.span {ι π} ≤ m :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hm_eq ▸ Ideal.mem_map_of_mem _ hπP))
  have hm_princ : Submodule.IsPrincipal m := by
    rw [le_antisymm hm_le hm_ge]; exact ⟨⟨ι π, rfl⟩⟩
  exact ((IsDiscreteValuationRing.TFAE L hnotfield).out 4 0).mp hm_princ

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[quotientPIR_to_integrallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma quotientPIR_to_integrallyClosed
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  CondQuotientPIR A → CondIntegrallyClosed A := by
-- proof
  intro h7
  rw [integrallyClosed_iff_dvrLocalizations]
  unfold CondDvrLocalizations
  haveI := quotientPIR_noetherian A h7
  exact {
    is_dvr_at_nonzero_prime := fun P hPne hPpr => quotientPIR_dvr A h7 P hPne hPpr
  }

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[integrallyClosed_to_twoGenerator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma integrallyClosed_to_twoGenerator
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h : CondIntegrallyClosed A) :
-- imply
  CondTwoGenerator A := by
-- proof
  unfold CondIntegrallyClosed at h; unfold CondTwoGenerator
  haveI := h
  intro I a _hI ha haI
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_eq_span_pair haI ha
  exact ⟨b, hb⟩

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[twoGenerator_to_quotientPIR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma twoGenerator_to_quotientPIR
  {A : Type*}
  [CommRing A]
  [IsDomain A]
-- given
  (h : CondTwoGenerator A) :
-- imply
  CondQuotientPIR A := by
-- proof
  unfold CondTwoGenerator at h; unfold CondQuotientPIR
  intro I hI
  constructor
  intro J
  rw [← map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J]
  set J' := comap (Ideal.Quotient.mk I) J
  have hIJ' : I ≤ J' := by
    intro x hx
    show (Ideal.Quotient.mk I) x ∈ J
    rwa [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hJ'ne : J' ≠ ⊥ := by
    intro hJ'
    have := hIJ' haI
    rw [hJ'] at this
    simp [Submodule.mem_bot] at this
    exact ha0 this
  obtain ⟨b, hb⟩ := h J' a hJ'ne ha0 (hIJ' haI)
  rw [hb, Ideal.map_span, Set.image_pair,
    Ideal.Quotient.eq_zero_iff_mem.mpr haI, Ideal.span_insert_zero]
  exact ⟨⟨(Ideal.Quotient.mk I) b, rfl⟩⟩

end DedekindDomainEquiv

namespace DedekindDomainEquiv

/--
[twoGenerator_to_integrallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma twoGenerator_to_integrallyClosed
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  CondTwoGenerator A → CondIntegrallyClosed A :=
-- proof
  fun h => quotientPIR_to_integrallyClosed A (twoGenerator_to_quotientPIR A h)
end DedekindDomainEquiv
open nonZeroDivisors
namespace FractionalIdealLocalization
section MapVersion


namespace FractionalIdealLocalization

/--
[localization_comm_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma localization_comm_add
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Field K']
  [Algebra A K]
  [Algebra A K']
  [IsFractionRing A K]
  [IsFractionRing A K']
  {I J : FractionalIdeal A⁰ K}
-- given
  (h : K ≃ₐ[A] K') :
-- imply
  FractionalIdeal.map (h : K →ₐ[A] K') (I + J) = FractionalIdeal.map (h : K →ₐ[A] K') I + FractionalIdeal.map (h : K →ₐ[A] K') J :=
-- proof
  FractionalIdeal.map_add I J (h : K →ₐ[A] K')

end FractionalIdealLocalization

namespace FractionalIdealLocalization

/--
[localization_comm_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma localization_comm_mul
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Field K']
  [Algebra A K]
  [Algebra A K']
  [IsFractionRing A K]
  [IsFractionRing A K']
  {I J : FractionalIdeal A⁰ K}
-- given
  (h : K ≃ₐ[A] K') :
-- imply
  FractionalIdeal.map (h : K →ₐ[A] K') (I * J) = FractionalIdeal.map (h : K →ₐ[A] K') I * FractionalIdeal.map (h : K →ₐ[A] K') J :=
-- proof
  FractionalIdeal.map_mul I J (h : K →ₐ[A] K')

end FractionalIdealLocalization

namespace FractionalIdealLocalization

/--
[localization_comm_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma localization_comm_div
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Field K]
  [Field K']
  [Algebra A K]
  [Algebra A K']
  [IsFractionRing A K]
  [IsFractionRing A K']
  {I J : FractionalIdeal A⁰ K}
-- given
  (h : K ≃ₐ[A] K') :
-- imply
  FractionalIdeal.map (h : K →ₐ[A] K') (I / J) = FractionalIdeal.map (h : K →ₐ[A] K') I / FractionalIdeal.map (h : K →ₐ[A] K') J :=
-- proof
  FractionalIdeal.map_div I J h

end FractionalIdealLocalization

namespace FractionalIdealLocalization

/--
[localization_atPrime_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma localization_atPrime_add
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {p : Ideal A}
  [p.IsPrime]
  {I J : FractionalIdeal (nonZeroDivisors A) (FractionRing A)} :
-- imply
  (I + J).extended (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) = I.extended (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) + J.extended (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) :=
-- proof
  FractionalIdeal.extended_add (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) I J

end FractionalIdealLocalization

namespace FractionalIdealLocalization

/--
[localization_atPrime_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma localization_atPrime_mul
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {p : Ideal A}
  [p.IsPrime]
  {I J : FractionalIdeal (nonZeroDivisors A) (FractionRing A)} :
-- imply
  (I * J).extended (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) = I.extended (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) * J.extended (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) :=
-- proof
  FractionalIdeal.extended_mul (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p) I J

end FractionalIdealLocalization

namespace FractionalIdealLocalization

/--
[localization_map_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
lemma localization_map_eq_id
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {p : Ideal A}
  [p.IsPrime] :
-- imply
  IsLocalization.map (FractionRing A) (algebraMap A (Localization.AtPrime p)) (nonZeroDivisors_le_comap_localizationAtPrime p) = RingHom.id (FractionRing A) := by
-- proof
  apply IsLocalization.ringHom_ext (R := A) (M := nonZeroDivisors A) (S := FractionRing A)
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [IsLocalization.map_eq]
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A)]

end FractionalIdealLocalization

/--
[nonZeroDivisors_le_comap_localizationAtPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean)
-/
@[path]
private lemma nonZeroDivisors_le_comap_localizationAtPrime_eq
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {p : Ideal A}
  [p.IsPrime] :
-- imply
  (nonZeroDivisors A) ≤ Submonoid.comap (algebraMap A (Localization.AtPrime p)) (nonZeroDivisors (Localization.AtPrime p)) := by
-- proof
  apply FractionalIdealLocalization.nonZeroDivisors_le_comap_localizationAtPrime p


-- created on 2026-10-23
-- updated on 2026-10-28
