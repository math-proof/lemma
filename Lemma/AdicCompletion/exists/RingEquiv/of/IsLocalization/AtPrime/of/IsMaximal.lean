import sympy.Basic
import Mathlib

/-!
Port of FLT `Def_PolynomialCompletion` (levelwise + localizationEquiv) and
`Def_AdicCompletionRingFunctoriality` (mapₐ / mapAlgEquiv), plus
`LocComplAux.map_maximalIdeal_le_of_ringEquiv` from the IsLocalization sol file.
-/

namespace AdicCompletion
namespace LocComplAux

theorem map_maximalIdeal_le_of_ringEquiv
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (e : R ≃+* S) :
    (IsLocalRing.maximalIdeal R).map e ≤ IsLocalRing.maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  intro hu
  exact hx (by simpa using hu.map e.symm)

end LocComplAux

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨c, rfl⟩ := mk_surjective I R x
  rw [evalₐ_mk, evalₐ_mk]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have h : c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := c.2 hle
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
  have h' : c n - c m ∈ I ^ m := by
    have := Submodule.neg_mem _ h
    rwa [neg_sub] at this
  exact Ideal.Quotient.eq.mpr h'

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

include he in
theorem levelwise_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp ((e n).toRingHom.comp (evalₐ I n).toRingHom) =
      (e m).toRingHom.comp (evalₐ I m).toRingHom := by
  ext x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [he, factorPow_evalₐ]

noncomputable def levelwiseHom : AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom) (levelwise_compat I J e he)

@[simp] theorem evalₐ_levelwiseHom (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (levelwiseHom I J e he x) = e n (evalₐ I n x) :=
  evalₐ_liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom)
    (levelwise_compat I J e he) n x

include he in
theorem he_symm {m n : ℕ} (h : m ≤ n) (y : S ⧸ J ^ n) :
    Ideal.Quotient.factorPow I h ((e n).symm y) = (e m).symm (Ideal.Quotient.factorPow J h y) := by
  apply (e m).injective
  rw [RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]

noncomputable def ofLevelwiseEquiv : AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (levelwiseHom I J e he)
    (levelwiseHom J I (fun n => (e n).symm) (he_symm I J e he))
    (RingHom.ext fun y => ext_evalₐ fun n => by simp)
    (RingHom.ext fun x => ext_evalₐ fun n => by simp)

@[simp] theorem evalₐ_ofLevelwiseEquiv (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (ofLevelwiseEquiv I J e he x) = e n (evalₐ I n x) :=
  evalₐ_levelwiseHom I J e he n x

theorem ofLevelwiseEquiv_of (x : R) (y : S)
    (hxy : ∀ n, e n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ y) :
    ofLevelwiseEquiv I J e he (of I R x) = of J S y := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_ofLevelwiseEquiv, evalₐ_of, evalₐ_of, hxy]

end Levelwise

end AdicCompletion

namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

theorem pow_le_comap_maximalIdeal_pow (n : ℕ) :
    q ^ n ≤ ((maximalIdeal (Localization.AtPrime q)) ^ n).comap
      (algebraMap R (Localization.AtPrime q)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  exact Ideal.le_comap_map

theorem comap_maximalIdeal_pow (n : ℕ) :
    ((maximalIdeal (Localization.AtPrime q)) ^ n).comap (algebraMap R (Localization.AtPrime q))
      = q ^ n := by
  rcases n with _ | n
  · simp
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  refine IsLocalization.under_map_of_isPrimary_disjoint q.primeCompl (Localization.AtPrime q)
    (Ideal.isPrimary_of_isMaximal_radical ?_) ?_
  · rw [Ideal.radical_pow _ n.succ_ne_zero, hq.isPrime.radical]
    exact hq
  · exact Set.disjoint_left.mpr fun x hx hx' => hx (Ideal.pow_le_self n.succ_ne_zero hx')

def quotientPowMap (n : ℕ) :
    R ⧸ q ^ n →+* Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime q)) ^ n :=
  Ideal.quotientMap _ (algebraMap R (Localization.AtPrime q)) (pow_le_comap_maximalIdeal_pow q n)

theorem quotientPowMap_mk (n : ℕ) (x : R) :
    quotientPowMap q n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R _ x) :=
  Ideal.quotientMap_mk

theorem exists_mul_add_eq_one_of_notMem (n : ℕ) {s : R} (hs : s ∉ q) :
    ∃ a, ∃ c ∈ q ^ n, a * s + c = 1 := by
  have htop : q ⊔ Ideal.span {s} = ⊤ := by
    obtain ⟨y, i, hi, h⟩ := hq.exists_inv hs
    rw [Ideal.eq_top_iff_one, ← h, sup_comm]
    exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.mpr ⟨y, rfl⟩) hi
  have h1 : (1 : R) ∈ q ^ n ⊔ Ideal.span {s} := by
    rw [Ideal.pow_sup_eq_top htop]; trivial
  obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨a, c, hc, by rw [add_comm, hcz]⟩

theorem quotientPowMap_bijective (n : ℕ) : Function.Bijective (quotientPowMap q n) := by
  constructor
  · exact Ideal.quotientMap_injective' (comap_maximalIdeal_pow q n).le
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, c, hc, hac⟩ := exists_mul_add_eq_one_of_notMem q n (s := (s : R)) s.prop
    refine ⟨Ideal.Quotient.mk _ (r * a), ?_⟩
    rw [quotientPowMap_mk, Ideal.Quotient.eq]
    have hs : (algebraMap R (Localization.AtPrime q)) (s : R) * IsLocalization.mk' _ r s
        = algebraMap R _ r := IsLocalization.mk'_spec' _ r s
    have : algebraMap R (Localization.AtPrime q) (r * a) - IsLocalization.mk' _ r s
        = - (IsLocalization.mk' (Localization.AtPrime q) r s * algebraMap R _ c) := by
      have hc' : algebraMap R (Localization.AtPrime q) (a * s) = 1 - algebraMap R _ c := by
        rw [eq_sub_iff_add_eq, ← map_add, hac, map_one]
      rw [map_mul, ← hs, mul_comm (algebraMap R _ (s : R)), mul_assoc, ← map_mul,
        mul_comm (s : R), hc']
      ring
    rw [this]
    refine neg_mem (Ideal.mul_mem_left _ _ ?_)
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc

noncomputable def quotientPowEquiv (n : ℕ) :
    R ⧸ q ^ n ≃+* Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime q)) ^ n :=
  RingEquiv.ofBijective _ (quotientPowMap_bijective q n)

@[simp] theorem quotientPowEquiv_mk (n : ℕ) (x : R) :
    quotientPowEquiv q n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R _ x) :=
  quotientPowMap_mk q n x

theorem factorPow_quotientPowEquiv {m n : ℕ} (h : m ≤ n) (x : R ⧸ q ^ n) :
    Ideal.Quotient.factorPow _ h (quotientPowEquiv q n x)
      = quotientPowEquiv q m (Ideal.Quotient.factorPow q h x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  show Ideal.Quotient.factor _ (quotientPowEquiv q n (Ideal.Quotient.mk _ x))
    = quotientPowEquiv q m (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ x))
  rw [quotientPowEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, quotientPowEquiv_mk]

end Localization.AtPrime

namespace AdicCompletion

variable {R : Type*} [CommRing R] (q : Ideal R) [q.IsMaximal]

open IsLocalRing

noncomputable def localizationEquiv :
    AdicCompletion q R ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :=
  ofLevelwiseEquiv q _ (Localization.AtPrime.quotientPowEquiv q)
    (Localization.AtPrime.factorPow_quotientPowEquiv q)

@[simp] theorem localizationEquiv_of (x : R) :
    localizationEquiv q (of q R x) = of _ _ (algebraMap R (Localization.AtPrime q) x) :=
  ofLevelwiseEquiv_of _ _ _ _ x _ fun n => Localization.AtPrime.quotientPowEquiv_mk q n x

section RingFunctoriality

universe u₀ u₁ u₂
variable {k : Type u₀} [CommRing k]
variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S]

section LevelMap

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

theorem pow_le_comap_pow (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

def levelMapₐ (h : I.map f ≤ J) (n : ℕ) : R ⧸ I ^ n →ₐ[k] S ⧸ J ^ n :=
  Ideal.quotientMapₐ (J ^ n) f (pow_le_comap_pow I J f h n)

@[simp]
theorem levelMapₐ_mk (h : I.map f ≤ J) (n : ℕ) (x : R) :
    levelMapₐ I J f h n (Ideal.Quotient.mk (I ^ n) x) = Ideal.Quotient.mk (J ^ n) (f x) :=
  rfl

theorem factorPow_levelMapₐ (h : I.map f ≤ J) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (levelMapₐ I J f h n x)
      = levelMapₐ I J f h m (Ideal.Quotient.factorPow I hmn x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end LevelMap

section Map

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

noncomputable def mapₐAux (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I R →ₐ[k] S ⧸ J ^ n :=
  (levelMapₐ I J f h n).comp ((evalₐ I n).restrictScalars k)

theorem mapₐAux_apply (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    mapₐAux I J f h n x = levelMapₐ I J f h n (evalₐ I n x) :=
  rfl

theorem factorₐ_comp_mapₐAux (h : I.map f ≤ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hle)).comp (mapₐAux I J f h n)
      = mapₐAux I J f h m := by
  ext x
  show Ideal.Quotient.factorPow J hle (levelMapₐ I J f h n (evalₐ I n x))
    = levelMapₐ I J f h m (evalₐ I m x)
  rw [factorPow_levelMapₐ, factorPow_evalₐ]

noncomputable def mapₐ (h : I.map f ≤ J) : AdicCompletion I R →ₐ[k] AdicCompletion J S :=
  liftAlgHom J (mapₐAux I J f h) (factorₐ_comp_mapₐAux I J f h)

@[simp]
theorem evalₐ_mapₐ (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (mapₐ I J f h x) = levelMapₐ I J f h n (evalₐ I n x) :=
  evalₐ_liftAlgHom J (mapₐAux I J f h) (factorₐ_comp_mapₐAux I J f h) n x

@[simp]
theorem mapₐ_of (h : I.map f ≤ J) (x : R) : mapₐ I J f h (of I R x) = of J S (f x) :=
  ext_evalₐ fun n => by rw [evalₐ_mapₐ, evalₐ_of, evalₐ_of, levelMapₐ_mk]

end Map

section Equiv

variable (I : Ideal R) (J : Ideal S)

noncomputable def mapAlgEquiv (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) :
    AdicCompletion I R ≃ₐ[k] AdicCompletion J S :=
  AlgEquiv.ofAlgHom (mapₐ I J (e : R →ₐ[k] S) he) (mapₐ J I (e.symm : S →ₐ[k] R) he')
    (AlgHom.ext fun y => ext_evalₐ fun n => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ J n y)
      rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_mapₐ, evalₐ_mapₐ, ← hz]
      show Ideal.Quotient.mk (J ^ n) (e (e.symm z)) = Ideal.Quotient.mk (J ^ n) z
      rw [AlgEquiv.apply_symm_apply])
    (AlgHom.ext fun x => ext_evalₐ fun n => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_mapₐ, evalₐ_mapₐ, ← hz]
      show Ideal.Quotient.mk (I ^ n) (e.symm (e z)) = Ideal.Quotient.mk (I ^ n) z
      rw [AlgEquiv.symm_apply_apply])

@[simp]
theorem mapAlgEquiv_apply (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) (x : AdicCompletion I R) :
    mapAlgEquiv I J e he he' x = mapₐ I J (e : R →ₐ[k] S) he x :=
  rfl

end Equiv

end RingFunctoriality

end AdicCompletion

/-!
Port of FLT Def_SemilocalAdicCompletion (Artinian device + semilocalComponent / semilocalPiEquiv).
Depends on mapₐ / evalₐ_mapₐ / levelMapₐ_mk / factorPow_evalₐ from the RingFunctoriality port above.
-/

universe u₁ u₂

section ArtinianDevice

variable {S : Type u₁} [CommRing S]

theorem isArtinian_of_finite_of_smul_eq_zero (I : Ideal S) [IsArtinianRing (S ⧸ I)]
    {M : Type u₂} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hann : ∀ i ∈ I, ∀ m : M, i • m = (0 : M)) : IsArtinian S M := by
  haveI hSI : IsArtinian S (S ⧸ I) :=
    isArtinian_of_surjective_algebraMap (R := S ⧸ I) (M := S ⧸ I)
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := M)

  have hker : ∀ i : Fin k, (I : Submodule S S) ≤
      LinearMap.ker (LinearMap.toSpanSingleton S M (s i)) := by
    intro i r hr
    simpa using hann r hr (s i)
  let ψ : ∀ _ : Fin k, (S ⧸ I) →ₗ[S] M :=
    fun i => Submodule.liftQ _ (LinearMap.toSpanSingleton S M (s i)) (hker i)
  let φ : (Fin k → S ⧸ I) →ₗ[S] M := LinearMap.lsum S (fun _ : Fin k => S ⧸ I) ℕ ψ
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hs, Submodule.span_le]
    rintro - ⟨i, rfl⟩
    refine ⟨Pi.single i (1 : S ⧸ I), ?_⟩
    simp only [φ, LinearMap.lsum_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · simp only [ψ, Pi.single_eq_same]
      rw [show (1 : S ⧸ I) = Submodule.Quotient.mk (1 : S) from rfl, Submodule.liftQ_apply]
      simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb, ψ]
    · simp
  exact isArtinian_of_surjective _ φ hφ

end ArtinianDevice

namespace Ideal

variable {S : Type u₁} [CommRing S]

theorem isArtinianRing_quotient_pow [IsNoetherianRing S] (I : Ideal S)
    [IsArtinianRing (S ⧸ I)] (n : ℕ) : IsArtinianRing (S ⧸ I ^ n) := by
  suffices h : IsArtinian S (S ⧸ I ^ n) by
    exact isArtinian_of_tower S h
  induction n with
  | zero =>
    haveI : Subsingleton (S ⧸ I ^ 0) :=
      ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
        Ideal.Quotient.eq.mpr (by simp [pow_zero, Ideal.one_eq_top])⟩
    infer_instance
  | succ n ih =>
    haveI := ih

    let q : (S ⧸ I ^ (n + 1)) →ₗ[S] S ⧸ I ^ n :=
      Submodule.factor (by
        exact_mod_cast Ideal.pow_le_pow_right (Nat.le_succ n))
    haveI : IsArtinian S (LinearMap.ker q) := by
      refine isArtinian_of_finite_of_smul_eq_zero I (fun i hi => ?_)
      rintro ⟨x, hx⟩
      refine Subtype.ext ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hr : r ∈ I ^ n := by
        simpa [q, Ideal.Quotient.eq_zero_iff_mem] using hx
      show i • Ideal.Quotient.mk (I ^ (n + 1)) r = 0
      have hmk : i • Ideal.Quotient.mk (I ^ (n + 1)) r =
          Ideal.Quotient.mk (I ^ (n + 1)) (i * r) := rfl
      rw [hmk, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
      exact Ideal.mul_mem_mul hi hr
    exact isArtinian_of_range_eq_ker (LinearMap.ker q).subtype q (Submodule.range_subtype _)

variable (I : Ideal S)

theorem isMaximal_of_isPrime_of_le [IsArtinianRing (S ⧸ I)] (Q : Ideal S) [hQ : Q.IsPrime]
    (hIQ : I ≤ Q) : Q.IsMaximal := by
  haveI : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIQ)
  haveI : (Q.map (Ideal.Quotient.mk I)).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime _
  have hQc : Q = (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (sup_eq_left.mpr hIQ).symm
  rw [hQc]
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem finite_setOf_isMaximal_and_le [IsArtinianRing (S ⧸ I)] :
    Finite {P : Ideal S // P.IsMaximal ∧ I ≤ P} := by
  refine Finite.of_surjective
    (f := fun Q : MaximalSpectrum (S ⧸ I) =>
      (⟨Q.asIdeal.comap (Ideal.Quotient.mk I),
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective,
        by simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using
          Ideal.ker_le_comap (Ideal.Quotient.mk I)⟩ :
        {P : Ideal S // P.IsMaximal ∧ I ≤ P})) ?_
  rintro ⟨P, hP, hIP⟩
  refine ⟨⟨P.map (Ideal.Quotient.mk I), ?_⟩, ?_⟩
  · haveI : (P.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hIP)
    exact IsArtinianRing.isMaximal_of_isPrime _
  · refine Subtype.ext ?_
    show (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP

theorem prod_pow_le_pow_of_radical_pow_le [IsArtinianRing (S ⧸ I)]
    {c n : ℕ} (hc : I.radical ^ c ≤ I ^ n) (s : Finset {P : Ideal S // P.IsMaximal ∧ I ≤ P})
    (hs : ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, P ∈ s) :
    (∏ P ∈ s, (P : Ideal S) ^ c) ≤ I ^ n := by
  have hprodrad : (∏ P ∈ s, (P : Ideal S)) ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hIQ, hQprime⟩
    haveI := hQprime
    have hQmax : Q.IsMaximal := isMaximal_of_isPrime_of_le I Q hIQ
    exact le_trans Ideal.prod_le_inf (Finset.inf_le (hs ⟨Q, hQmax, hIQ⟩))
  calc (∏ P ∈ s, (P : Ideal S) ^ c)
      = (∏ P ∈ s, (P : Ideal S)) ^ c := Finset.prod_pow s c _
    _ ≤ I.radical ^ c := Ideal.pow_right_mono hprodrad c
    _ ≤ I ^ n := hc

theorem sup_pow_le_pow_of_le {P : Ideal S} (hIP : I ≤ P) {m n : ℕ} (hnm : n ≤ m) :
    I ^ n ⊔ P ^ m ≤ P ^ n :=
  sup_le (Ideal.pow_right_mono hIP n) (Ideal.pow_le_pow_right hnm)

theorem sup_mul_sup_le (A B C : Ideal S) : (A ⊔ B) * (A ⊔ C) ≤ A ⊔ B * C := by
  rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact le_trans Ideal.mul_le_left le_sup_left
  · exact le_trans Ideal.mul_le_right le_sup_left
  · exact le_trans Ideal.mul_le_left le_sup_left
  · exact le_sup_right

theorem isCoprime_sup_pow_of_ne [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    {P Q : {P : Ideal S // P.IsMaximal ∧ I ≤ P}} (hPQ : P ≠ Q) :
    IsCoprime (I ^ n ⊔ (P : Ideal S) ^ c) (I ^ n ⊔ (Q : Ideal S) ^ c) := by
  have hPQ' : (⟨(P : Ideal S), P.2.1⟩ : MaximalSpectrum S) ≠ ⟨(Q : Ideal S), Q.2.1⟩ := by
    intro h
    exact hPQ (Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
  have h1 : IsCoprime ((P : Ideal S) ^ c) ((Q : Ideal S) ^ c) :=
    (MaximalSpectrum.isCoprime_of_ne hPQ').pow
  rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
  rw [eq_top_iff, ← h1]
  exact sup_le (le_trans le_sup_right le_sup_left) (le_sup_of_le_right le_sup_right)

theorem iInf_sup_pow_eq [IsArtinianRing (S ⧸ I)] {c n : ℕ} (hc : I.radical ^ c ≤ I ^ n) :
    ⨅ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, (I ^ n ⊔ (P : Ideal S) ^ c) = I ^ n := by
  refine le_antisymm ?_ (le_iInf fun P => le_sup_left)
  by_cases hI : I = ⊤
  · subst hI
    simp [Ideal.top_pow]
  · haveI := finite_setOf_isMaximal_and_le I
    haveI := Fintype.ofFinite {P : Ideal S // P.IsMaximal ∧ I ≤ P}
    classical
    have key : ∀ t : Finset {P : Ideal S // P.IsMaximal ∧ I ≤ P},
        (⨅ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, (I ^ n ⊔ (P : Ideal S) ^ c)) ≤
          I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert Q t hQt ih =>
        have hcop : IsCoprime (I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c)
            (I ^ n ⊔ (Q : Ideal S) ^ c) := by
          have hfac : IsCoprime (∏ P ∈ t, (P : Ideal S) ^ c) ((Q : Ideal S) ^ c) := by
            refine IsCoprime.prod_left fun P hPt => ?_
            have hPQ : P ≠ Q := fun h => hQt (h ▸ hPt)
            have hPQ' : (⟨(P : Ideal S), P.2.1⟩ : MaximalSpectrum S) ≠
                ⟨(Q : Ideal S), Q.2.1⟩ := by
              intro h
              exact hPQ (Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
            exact (MaximalSpectrum.isCoprime_of_ne hPQ').pow
          rw [Ideal.isCoprime_iff_sup_eq] at hfac ⊢
          rw [eq_top_iff, ← hfac]
          exact sup_le (le_trans le_sup_right le_sup_left) (le_sup_of_le_right le_sup_right)
        calc (⨅ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, (I ^ n ⊔ (P : Ideal S) ^ c))
            ≤ (I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c) ⊓ (I ^ n ⊔ (Q : Ideal S) ^ c) :=
              le_inf ih (iInf_le _ Q)
          _ = (I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c) * (I ^ n ⊔ (Q : Ideal S) ^ c) :=
              (Ideal.mul_eq_inf_of_isCoprime hcop).symm
          _ ≤ I ^ n ⊔ (∏ P ∈ t, (P : Ideal S) ^ c) * (Q : Ideal S) ^ c :=
              sup_mul_sup_le _ _ _
          _ = I ^ n ⊔ ∏ P ∈ insert Q t, (P : Ideal S) ^ c := by
              rw [Finset.prod_insert hQt, mul_comm]
    refine le_trans (key Finset.univ) ?_
    refine sup_le le_rfl ?_
    exact prod_pow_le_pow_of_radical_pow_le I hc Finset.univ fun P => Finset.mem_univ P

noncomputable def quotientPowEquivPiSup [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) :
    (S ⧸ I ^ n) ≃+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, S ⧸ (I ^ n ⊔ (P : Ideal S) ^ c) :=
  haveI := finite_setOf_isMaximal_and_le I
  (Ideal.quotEquivOfEq (iInf_sup_pow_eq I hc).symm).trans
    (Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hPQ => isCoprime_sup_pow_of_ne I hPQ)

theorem quotientPowEquivPiSup_mk [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) (x : S) :
    quotientPowEquivPiSup I hc (Ideal.Quotient.mk _ x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.mk (I ^ n ⊔ (P : Ideal S) ^ c) x := by
  funext _P
  simp [quotientPowEquivPiSup, Ideal.quotientInfRingEquivPiQuotient,
    Ideal.quotientInfToPiQuotient]

end Ideal

section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

theorem map_algHom_id_le {P : Ideal S} (hIP : I ≤ P) :
    I.map (AlgHom.id S S) ≤ P := by
  simp [hIP]

noncomputable def semilocalComponent {P : Ideal S} (hIP : I ≤ P) :
    AdicCompletion I S →ₐ[S] AdicCompletion P S :=
  mapₐ I P (AlgHom.id S S) (map_algHom_id_le I hIP)

theorem semilocalComponent_of {P : Ideal S} (hIP : I ≤ P) (x : S) :
    semilocalComponent I hIP (of I S x) = of P S x := by
  simp [semilocalComponent]

noncomputable def semilocalPiHom :
    AdicCompletion I S →+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal S) S :=
  RingHom.pi fun P => (semilocalComponent I P.2.2).toRingHom

theorem semilocalPiHom_apply (x : AdicCompletion I S)
    (P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}) :
    semilocalPiHom I x P = semilocalComponent I P.2.2 x := rfl

theorem semilocalPiHom_of (x : S) :
    semilocalPiHom I (of I S x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} => of (P : Ideal S) S x := by
  funext P
  exact semilocalComponent_of I P.2.2 x

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal S) = I ^ n := by
  ext x; simp

noncomputable def ofCompatibleFamily (z : ∀ n, S ⧸ I ^ n)
    (hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m) :
    AdicCompletion I S :=
  ⟨fun n => Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n), by
    intro m n hmn
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z n)
    have hzm : z m = Ideal.Quotient.mk (I ^ m) r := by
      rw [← hz hmn, ← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    show transitionMap I S hmn (Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n)) =
      Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I m).symm (z m)
    rw [← hr, hzm, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
    rfl⟩

theorem evalₐ_ofCompatibleFamily (z : ∀ n, S ⧸ I ^ n)
    (hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m) (n : ℕ) :
    evalₐ I n (ofCompatibleFamily I z hz) = z n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z n)
  rw [← hr]
  show Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n)
      (eval I S n (ofCompatibleFamily I z hz)) = Ideal.Quotient.mk (I ^ n) r
  rw [show eval I S n (ofCompatibleFamily I z hz) =
      Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n) from rfl,
    ← hr, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]

variable [IsNoetherianRing S] [IsArtinianRing (S ⧸ I)]

omit [IsArtinianRing (S ⧸ I)] in

theorem exists_uniform_exponent :
    ∃ c₁ : ℕ, (∀ n : ℕ, I.radical ^ (c₁ * n) ≤ I ^ n) ∧ (∀ n : ℕ, n ≤ c₁ * n) := by
  obtain ⟨c₀, hc₀⟩ := Ideal.exists_radical_pow_le_of_fg I (IsNoetherian.noetherian _)
  refine ⟨c₀ + 1, fun n => ?_, fun n => Nat.le_mul_of_pos_left n c₀.succ_pos⟩
  rw [pow_mul]
  refine Ideal.pow_right_mono ?_ n
  rw [pow_succ]
  exact le_trans Ideal.mul_le_left hc₀

theorem semilocalPiHom_injective : Function.Injective (semilocalPiHom I) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  refine ext_evalₐ fun n => ?_
  have hz : evalₐ I n (0 : AdicCompletion I S) = 0 := by simp
  rw [hz]
  obtain ⟨c₁, hrad, hle⟩ := exists_uniform_exponent I
  refine (Ideal.quotientPowEquivPiSup I (hrad n)).injective ?_
  change Ideal.quotientPowEquivPiSup I (hrad n) (evalₐ I n x) = 0
  funext P
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I (c₁ * n) x)
  have hev : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factorPow_evalₐ I (hle n) x, ← hr, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
  have hP0 : evalₐ (P : Ideal S) (c₁ * n) (semilocalPiHom I x P) = 0 := by
    simp [congrFun hx P, Pi.zero_apply]
  rw [semilocalPiHom_apply, semilocalComponent, evalₐ_mapₐ, ← hr, levelMapₐ_mk] at hP0
  have hrP : r ∈ (P : Ideal S) ^ (c₁ * n) := by
    rwa [AlgHom.coe_id, id_eq, Ideal.Quotient.eq_zero_iff_mem] at hP0
  rw [hev, Ideal.quotientPowEquivPiSup_mk, Pi.zero_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hrP)

omit [IsNoetherianRing S] in

theorem quotientPowEquivPiSup_factorPow {c n c' n' : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) (hc' : I.radical ^ c' ≤ I ^ n')
    (hn : n ≤ n') (hcc : c ≤ c') (z : S ⧸ I ^ n') :
    Ideal.quotientPowEquivPiSup I hc (Ideal.Quotient.factorPow I hn z) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.factor
          (sup_le_sup (Ideal.pow_le_pow_right hn) (Ideal.pow_le_pow_right hcc))
          (Ideal.quotientPowEquivPiSup I hc' z P) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective z
  funext P
  rw [← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.quotientPowEquivPiSup_mk, Ideal.quotientPowEquivPiSup_mk,
    Ideal.Quotient.factor_mk]

theorem semilocalPiHom_surjective : Function.Surjective (semilocalPiHom I) := by
  intro y
  obtain ⟨c₁, hrad, hle⟩ := exists_uniform_exponent I
  have hmono : ∀ {m n : ℕ}, m ≤ n → c₁ * m ≤ c₁ * n := fun h => Nat.mul_le_mul_left _ h

  set z : ∀ n, S ⧸ I ^ n := fun n =>
    (Ideal.quotientPowEquivPiSup I (hrad n)).symm
      (fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * n) (y P)))
    with hz_def
  have hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m := by
    intro m n hmn
    refine (Ideal.quotientPowEquivPiSup I (hrad m)).injective ?_
    rw [RingEquiv.apply_symm_apply,
      quotientPowEquivPiSup_factorPow I (hrad m) (hrad n) hmn (hmono hmn),
      RingEquiv.apply_symm_apply]
    funext P
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (P : Ideal S) (c₁ * n) (y P))
    have hsm : evalₐ (P : Ideal S) (c₁ * m) (y P) =
        Ideal.Quotient.mk ((P : Ideal S) ^ (c₁ * m)) s := by
      rw [← factorPow_evalₐ (P : Ideal S) (hmono hmn) (y P), ← hs,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← hs, hsm, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk]
  refine ⟨ofCompatibleFamily I z hz, ?_⟩
  funext P
  refine ext_evalₐ fun k => ?_

  rw [semilocalPiHom_apply, semilocalComponent, evalₐ_mapₐ, evalₐ_ofCompatibleFamily]

  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z k)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (P : Ideal S) (c₁ * k) (y P))
  have hcomp : Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) r =
      Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) s := by
    have hzk : Ideal.quotientPowEquivPiSup I (hrad k) (z k) P =
        Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * k) (y P)) :=
      congrFun ((Ideal.quotientPowEquivPiSup I (hrad k)).apply_symm_apply
        (fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
          Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * k) (y P)))) P
    have hzk' : Ideal.quotientPowEquivPiSup I (hrad k) (z k) P =
        Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) r := by
      rw [← hr, Ideal.quotientPowEquivPiSup_mk]
    rw [← hzk', hzk, ← hs, Ideal.Quotient.factor_mk]
  have hrs : r - s ∈ (P : Ideal S) ^ k := by
    have hmem : r - s ∈ I ^ k ⊔ (P : Ideal S) ^ (c₁ * k) :=
      (Ideal.Quotient.eq).mp hcomp
    exact Ideal.sup_pow_le_pow_of_le I P.2.2 (hle k) hmem
  rw [← hr, levelMapₐ_mk, AlgHom.coe_id, id_eq,
    ← factorPow_evalₐ (P : Ideal S) (hle k) (y P), ← hs,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  exact (Ideal.Quotient.eq).mpr hrs

noncomputable def semilocalPiEquiv :
    AdicCompletion I S ≃+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal S) S :=
  RingEquiv.ofBijective (semilocalPiHom I)
    ⟨semilocalPiHom_injective I, semilocalPiHom_surjective I⟩

theorem semilocalPiEquiv_of (x : S) :
    semilocalPiEquiv I (of I S x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} => of (P : Ideal S) S x :=
  semilocalPiHom_of I x

theorem semilocalPiEquiv_apply {𝔫 : Ideal S} [h𝔫 : 𝔫.IsMaximal] (hI : I ≤ 𝔫)
    (y : AdicCompletion I S) :
    semilocalPiEquiv I y ⟨𝔫, h𝔫, hI⟩ = semilocalComponent I hI y :=
  semilocalPiHom_apply I y ⟨𝔫, h𝔫, hI⟩


end AdicCompletion


/-!
Ports of FLT Def_AdicCompletionRestrictScalars, Def_AdicCompletionTensorRing
(completionBaseChangeHom / tensorRingEquiv), and GaloisAction LiesOver algebra.
-/

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem restrictScalars_map_pow_smul_top (n : ℕ) :
    (((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A) =
      (𝔭 ^ n • ⊤ : Submodule A B) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

noncomputable def levelRestrictScalarsEquiv (n : ℕ) :
    (B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) ≃ₗ[A]
      B ⧸ (𝔭 ^ n • ⊤ : Submodule A B) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_map_pow_smul_top B 𝔭 n))

theorem levelRestrictScalarsEquiv_mk (n : ℕ) (b : B) :
    levelRestrictScalarsEquiv B 𝔭 n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b :=
  rfl

theorem transitionMap_levelRestrictScalarsEquiv {m n : ℕ} (hmn : m ≤ n)
    (y : B ⧸ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :
    transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n y) =
      levelRestrictScalarsEquiv B 𝔭 m
        (transitionMap (𝔭.map (algebraMap A B)) B hmn y) :=
  Quotient.inductionOn' y fun _ => rfl

noncomputable def restrictScalarsEquiv :
    AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A] AdicCompletion 𝔭 B where
  toFun x := ⟨fun n => levelRestrictScalarsEquiv B 𝔭 n (x.val n), fun {m n} hmn => by
    show transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n (x.val n)) =
      levelRestrictScalarsEquiv B 𝔭 m (x.val m)
    rw [← x.prop hmn]
    exact transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn (x.val n)⟩
  invFun y := ⟨fun n => (levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n), fun {m n} hmn => by
    show transitionMap (𝔭.map (algebraMap A B)) B hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)) =
      (levelRestrictScalarsEquiv B 𝔭 m).symm (y.val m)
    rw [← y.prop hmn, LinearEquiv.eq_symm_apply,
      ← transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)),
      LinearEquiv.apply_symm_apply]⟩
  map_add' x y := by
    ext n
    exact map_add (levelRestrictScalarsEquiv B 𝔭 n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (levelRestrictScalarsEquiv B 𝔭 n) a _
  left_inv x := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).apply_symm_apply _

theorem restrictScalarsEquiv_of (b : B) :
    restrictScalarsEquiv B 𝔭 (of (𝔭.map (algebraMap A B)) B b) = of 𝔭 B b := by
  ext n
  rfl

theorem restrictScalarsEquiv_symm_of (b : B) :
    (restrictScalarsEquiv B 𝔭).symm (of 𝔭 B b) = of (𝔭.map (algebraMap A B)) B b := by
  ext n
  rfl

end AdicCompletion

open scoped TensorProduct

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def completionBaseChangeHom :
    AdicCompletion 𝔭 A →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  mapₐ 𝔭 (𝔭.map (algebraMap A B)) (Algebra.ofId A B)
    (le_of_eq (rfl : 𝔭.map (Algebra.ofId A B) = 𝔭.map (algebraMap A B)))

@[simp]
theorem completionBaseChangeHom_of (x : A) :
    completionBaseChangeHom B 𝔭 (of 𝔭 A x) =
      of (𝔭.map (algebraMap A B)) B (algebraMap A B x) := by
  simp [completionBaseChangeHom, Algebra.ofId_apply]

noncomputable def completionOfAlgHom :
    B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  IsScalarTower.toAlgHom A B _

@[simp]
theorem completionOfAlgHom_apply (b : B) :
    completionOfAlgHom B 𝔭 b = of (𝔭.map (algebraMap A B)) B b := rfl

noncomputable def tensorRingHom :
    (AdicCompletion 𝔭 A) ⊗[A] B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  Algebra.TensorProduct.productMap (completionBaseChangeHom B 𝔭) (completionOfAlgHom B 𝔭)

@[simp]
theorem tensorRingHom_tmul (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingHom B 𝔭 (x ⊗ₜ[A] b) =
      completionBaseChangeHom B 𝔭 x * of (𝔭.map (algebraMap A B)) B b := by
  simp [tensorRingHom]

theorem tensorRingHom_tmul_eq_symm_smul (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingHom B 𝔭 (x ⊗ₜ[A] b) =
      (restrictScalarsEquiv B 𝔭).symm (x • of 𝔭 B b) := by
  induction x using AdicCompletion.induction_on with
  | _ a =>
    refine ext_evalₐ fun n => ?_

    rw [tensorRingHom_tmul, map_mul]
    simp only [completionBaseChangeHom, evalₐ_mapₐ, evalₐ_mk, levelMapₐ_mk,
      Algebra.ofId_apply, evalₐ_of]

    have hval : (mk 𝔭 A a • of 𝔭 B b).val n =
        Submodule.Quotient.mk (a.val n • b) := by
      rw [smul_eval]
      show Ideal.Quotient.mk (𝔭 ^ n • ⊤ : Ideal A) (a.val n) •
          Submodule.Quotient.mk (p := (𝔭 ^ n • ⊤ : Submodule A B)) b = _
      rw [mk_smul_mk, ← Submodule.Quotient.mk_smul]
    have hsymmval : ((restrictScalarsEquiv B 𝔭).symm (mk 𝔭 A a • of 𝔭 B b)).val n =
        Submodule.Quotient.mk (p :=
          ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) (a.val n • b) := by
      show (levelRestrictScalarsEquiv B 𝔭 n).symm ((mk 𝔭 A a • of 𝔭 B b).val n) = _
      rw [hval, LinearEquiv.symm_apply_eq, levelRestrictScalarsEquiv_mk]
    rw [← factor_eval_eq_evalₐ _ _ (le_of_eq (by ext x; simp)),
      show eval (𝔭.map (algebraMap A B)) B n
        ((restrictScalarsEquiv B 𝔭).symm (mk 𝔭 A a • of 𝔭 B b)) =
        ((restrictScalarsEquiv B 𝔭).symm (mk 𝔭 A a • of 𝔭 B b)).val n from rfl,
      hsymmval,
      show Submodule.Quotient.mk (p :=
          ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) (a.val n • b) =
        Submodule.mkQ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B) (a.val n • b)
        from rfl,
      Submodule.factor_mk, ← map_mul, Algebra.smul_def]
    rfl

theorem restrictScalarsEquiv_tensorRingHom (z : AdicCompletion 𝔭 A ⊗[A] B) :
    restrictScalarsEquiv B 𝔭 (tensorRingHom B 𝔭 z) = ofTensorProduct 𝔭 B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    rw [tensorRingHom_tmul_eq_symm_smul, LinearEquiv.apply_symm_apply,
      ofTensorProduct_tmul]
  | add u v hu hv => simp [map_add, hu, hv]

end AdicCompletion

section SameUniverse

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₁) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem tensorRingHom_bijective [IsNoetherianRing A] [Module.Finite A B] :
    Function.Bijective (tensorRingHom B 𝔭) := by
  have hfun : ⇑(tensorRingHom B 𝔭) =
      ⇑(restrictScalarsEquiv B 𝔭).symm ∘ ⇑(ofTensorProduct 𝔭 B) := by
    funext z
    rw [Function.comp_apply, ← restrictScalarsEquiv_tensorRingHom B 𝔭 z,
      LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (restrictScalarsEquiv B 𝔭).symm.bijective.comp
    (ofTensorProduct_bijective_of_finite_of_isNoetherian 𝔭 B)

noncomputable def tensorRingEquiv [IsNoetherianRing A] [Module.Finite A B] :
    (AdicCompletion 𝔭 A ⊗[A] B) ≃ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  AlgEquiv.ofBijective (tensorRingHom B 𝔭) (tensorRingHom_bijective B 𝔭)

@[simp]
theorem tensorRingEquiv_tmul [IsNoetherianRing A] [Module.Finite A B]
    (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingEquiv B 𝔭 (x ⊗ₜ[A] b) =
      completionBaseChangeHom B 𝔭 x * of (𝔭.map (algebraMap A B)) B b :=
  tensorRingHom_tmul B 𝔭 x b

end AdicCompletion

end SameUniverse


namespace AdicCompletion
section LiesOverAlgebra
variable {O : Type*} [CommRing O] {C : Type*} [CommRing C] [Algebra O C]
variable (J : Ideal O) (𝔫 : Ideal C)

theorem map_ofId_le_of_liesOver [h𝔫 : 𝔫.LiesOver J] : J.map (Algebra.ofId O C) ≤ 𝔫 := by
  rw [Ideal.map_le_iff_le_comap]
  intro o ho
  rw [h𝔫.over] at ho
  exact ho

noncomputable def algHomOfLiesOver [𝔫.LiesOver J] :
    AdicCompletion J O →ₐ[O] AdicCompletion 𝔫 C :=
  mapₐ J 𝔫 (Algebra.ofId O C) (map_ofId_le_of_liesOver J 𝔫)

@[reducible]
noncomputable def instAlgebraOfLiesOver [𝔫.LiesOver J] :
    Algebra (AdicCompletion J O) (AdicCompletion 𝔫 C) :=
  (algHomOfLiesOver J 𝔫).toRingHom.toAlgebra

attribute [instance low] instAlgebraOfLiesOver

theorem algebraMap_eq_algHomOfLiesOver [𝔫.LiesOver J] (x : AdicCompletion J O) :
    algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) x = algHomOfLiesOver J 𝔫 x :=
  rfl

theorem evalₐ_algebraMap_of_liesOver [𝔫.LiesOver J] (n : ℕ) (o : O) (x : AdicCompletion J O)
    (hx : evalₐ J n x = Ideal.Quotient.mk (J ^ n) o) :
    evalₐ 𝔫 n (algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) x)
      = Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) := by
  rw [algebraMap_eq_algHomOfLiesOver, algHomOfLiesOver, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

theorem semilocalComponent_completionBaseChangeHom_eq_algebraMap
    [IsLocalRing O] (𝔪 : Ideal O) (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver 𝔪]
    (hI : (𝔪.map (algebraMap O C)) ≤ 𝔫) (x : AdicCompletion 𝔪 O) :
    semilocalComponent (𝔪.map (algebraMap O C)) hI (completionBaseChangeHom C 𝔪 x) =
      algebraMap (AdicCompletion 𝔪 O) (AdicCompletion 𝔫 C) x := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔪 n x)
  have hL : evalₐ 𝔫 n (semilocalComponent (𝔪.map (algebraMap O C)) hI
      (completionBaseChangeHom C 𝔪 x)) =
      Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) := by
    rw [semilocalComponent, completionBaseChangeHom, evalₐ_mapₐ, evalₐ_mapₐ, ← ho,
      levelMapₐ_mk, levelMapₐ_mk]
    simp [Algebra.ofId_apply]
  have hR : evalₐ 𝔫 n (algebraMap (AdicCompletion 𝔪 O) (AdicCompletion 𝔫 C) x) =
      Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) :=
    evalₐ_algebraMap_of_liesOver 𝔪 𝔫 n o x ho.symm
  exact hL.trans hR.symm

end LiesOverAlgebra
end AdicCompletion

/--
[AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal.lean)
-/
@[path]
private lemma main
  {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
-- given
  (𝔓 : Ideal B) [𝔓.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S 𝔓] :
-- imply
  ∃ T : AdicCompletion 𝔓 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ b : B, T (algebraMap B (AdicCompletion 𝔓 B) b)
        = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap B S b) := by
-- proof
  let L := Localization.AtPrime 𝔓
  let e : L ≃ₐ[B] S := IsLocalization.algEquiv 𝔓.primeCompl L S
  have he : (IsLocalRing.maximalIdeal L).map (e : L →ₐ[B] S) ≤ IsLocalRing.maximalIdeal S :=
    AdicCompletion.LocComplAux.map_maximalIdeal_le_of_ringEquiv e.toRingEquiv
  have he' : (IsLocalRing.maximalIdeal S).map (e.symm : S →ₐ[B] L) ≤ IsLocalRing.maximalIdeal L :=
    AdicCompletion.LocComplAux.map_maximalIdeal_le_of_ringEquiv e.symm.toRingEquiv
  let T₂ : AdicCompletion (IsLocalRing.maximalIdeal L) L ≃ₐ[B] AdicCompletion (IsLocalRing.maximalIdeal S) S :=
    AdicCompletion.mapAlgEquiv (IsLocalRing.maximalIdeal L) (IsLocalRing.maximalIdeal S) e he he'
  refine ⟨(AdicCompletion.localizationEquiv 𝔓).trans T₂.toRingEquiv, fun b => ?_⟩
  rw [RingEquiv.trans_apply]
  change T₂ (AdicCompletion.localizationEquiv 𝔓 (AdicCompletion.of 𝔓 B b)) =
    AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap B S b)
  rw [AdicCompletion.localizationEquiv_of]
  change AdicCompletion.mapAlgEquiv (IsLocalRing.maximalIdeal L) (IsLocalRing.maximalIdeal S) e he he'
    (AdicCompletion.of _ _ (algebraMap B L b)) = _
  rw [AdicCompletion.mapAlgEquiv_apply, AdicCompletion.mapₐ_of]
  congr 1
  exact e.commutes b

-- created on 2026-10-09
