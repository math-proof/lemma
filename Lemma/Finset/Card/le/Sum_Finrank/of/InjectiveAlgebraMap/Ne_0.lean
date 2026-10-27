import Mathlib
import Initialize.Tactic.Attr.Basic


private lemma card_emb_le_finrank
  [Field C]
  [CommRing T]
  {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [Algebra Ô C] [Algebra Ô T] [Module.Free Ô T] [Module.Finite Ô T]
  {Φ : Finset (T →ₐ[Ô] C)} :
-- imply
  Φ.card ≤ Module.finrank Ô T := by
-- proof
  classical
  let _ := Module.Free.ChooseBasisIndex.fintype Ô T
  let b := Module.Free.chooseBasis Ô T
  have hli : LinearIndependent C (fun φ : Φ => fun i => (φ : T →ₐ[Ô] C) (b i)) := by
    have h0 : LinearIndependent C (fun φ : Φ => ((φ : T →ₐ[Ô] C) : T → C)) := by
      apply (linearIndependent_monoidHom T C).comp (fun φ : Φ => (φ : T →ₐ[Ô] C).toMonoidHom)
      intro φ ψ h
      apply Subtype.ext
      apply AlgHom.ext
      intro t
      apply DFunLike.congr_fun h t
    rw [linearIndependent_iff'] at h0 ⊢
    intro s g hg φ hφ
    apply h0 s g _ φ hφ
    ext t
    have hgi : ∀ i, ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) = 0 := fun i => by
      have := congr_fun hg i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    have ht : ∀ ψ : T →ₐ[Ô] C, ψ t = ∑ i, algebraMap Ô C (b.repr t i) * ψ (b i) := by
      intro ψ
      conv_lhs => rw [← b.sum_repr t]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Algebra.smul_def]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∑ ψ ∈ s, g ψ * (algebraMap Ô C (b.repr t i) * (ψ : T →ₐ[Ô] C) (b i)) =
      algebraMap Ô C (b.repr t i) * ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      ring
    rw [this, hgi i, mul_zero]
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_fintype_fun_eq_card] at hcard
  rw [Module.finrank_eq_card_chooseBasisIndex]
  apply hcard

private lemma comap_ker_eq_bot
  [Field C]
  {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [Algebra Ô C]
  {S : Type u} [CommRing S] [Algebra Ô S]
  {φ : S →ₐ[Ô] C}
-- given
  (hinj : Function.Injective (algebraMap Ô C)) :
-- imply
  (RingHom.ker φ.toRingHom).comap (algebraMap Ô S) = ⊥ := by
-- proof
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] at ha
  rw [Ideal.mem_bot]
  apply hinj (ha.trans (map_zero _).symm)

private lemma algebraMap_quotient_ker_injective
  [Field C]
  {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [Algebra Ô C]
  {S : Type u} [CommRing S] [Algebra Ô S]
  {φ : S →ₐ[Ô] C}
-- given
  (hinj : Function.Injective (algebraMap Ô C)) :
-- imply
  Function.Injective (algebraMap Ô (S ⧸ RingHom.ker φ.toRingHom)) := by
-- proof
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [IsScalarTower.algebraMap_apply Ô S (S ⧸ RingHom.ker φ.toRingHom), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have : a ∈ (RingHom.ker φ.toRingHom).comap (algebraMap Ô S) := ha
  rwa [comap_ker_eq_bot hinj, Ideal.mem_bot] at this

private lemma ker_mem_minimalPrimes
  [Field C]
  {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [Algebra Ô C]
  {S : Type u} [CommRing S] [Algebra Ô S] [Module.Finite Ô S]
  {φ : S →ₐ[Ô] C}
-- given
  (hinj : Function.Injective (algebraMap Ô C)) :
-- imply
  RingHom.ker φ.toRingHom ∈ minimalPrimes S := by
-- proof
  set P := RingHom.ker φ.toRingHom with hP
  let _ : P.IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hqP
  let _ := hq
  have hPq : (P.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomap : (P.map (Ideal.Quotient.mk q)).comap (algebraMap Ô (S ⧸ q)) = ⊥ := by
    rw [IsScalarTower.algebraMap_eq Ô S (S ⧸ q), Ideal.Quotient.algebraMap_eq, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hqP]
    apply comap_ker_eq_bot hinj
  have h0 : P.map (Ideal.Quotient.mk q) = ⊥ := Ideal.eq_bot_of_under_eq_bot hcomap
  intro s hs
  have : Ideal.Quotient.mk q s ∈ P.map (Ideal.Quotient.mk q) := Ideal.mem_map_of_mem _ hs
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  apply this

private lemma card_filter_ker_eq_le
  [Field C]
  {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô] [Algebra Ô C]
  {S : Type u} [CommRing S] [Algebra Ô S] [Module.Finite Ô S]
  {𝔓 : Ideal S} [𝔓.IsPrime]
  {Φ : Finset (S →ₐ[Ô] C)}
-- given
  (hinj : Function.Injective (algebraMap Ô (S ⧸ 𝔓))) :
-- imply
  (Φ.filter (fun φ => RingHom.ker φ.toRingHom = 𝔓)).card ≤ Module.finrank Ô (S ⧸ 𝔓) := by
-- proof
  classical
  let _ : Module.IsTorsionFree Ô (S ⧸ 𝔓) := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  let _ : Module.Free Ô (S ⧸ 𝔓) := Module.free_of_finite_type_torsion_free'
  set F := Φ.filter (fun φ => RingHom.ker φ.toRingHom = 𝔓) with hF
  have hlift : ∀ φ ∈ F, ∀ a ∈ 𝔓, (φ : S →ₐ[Ô] C) a = 0 := by
    intro φ hφ a ha
    rw [hF, Finset.mem_filter] at hφ
    rw [← hφ.2] at ha
    apply ha
  let L : F → ((S ⧸ 𝔓) →ₐ[Ô] C) := fun φ => Ideal.Quotient.liftₐ 𝔓 (φ : S →ₐ[Ô] C) (hlift φ φ.2)
  have hL : Function.Injective L := by
    intro φ ψ h
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    have heq := DFunLike.congr_fun h (Ideal.Quotient.mk 𝔓 s)
    have hφ := Ideal.Quotient.liftₐ_comp (R₁ := Ô) 𝔓 (φ : S →ₐ[Ô] C) (hlift φ φ.2)
    have hψ := Ideal.Quotient.liftₐ_comp (R₁ := Ô) 𝔓 (ψ : S →ₐ[Ô] C) (hlift ψ ψ.2)
    have hφs := DFunLike.congr_fun hφ s
    have hψs := DFunLike.congr_fun hψ s
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hφs hψs
    rw [← hφs, ← hψs]
    apply heq
  have h1 := card_emb_le_finrank (T := S ⧸ 𝔓) (Φ := Finset.univ.image L)
  rw [Finset.card_image_of_injective _ hL, Finset.card_univ, Fintype.card_coe] at h1
  apply h1


/--
[Algebra_card_algHom_le_finsum_finrank_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_card_algHom_le_finsum_finrank_quotient.lean)
-/
@[path]
private lemma main
  {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
  {S : Type u} [CommRing S] [Algebra Ô S] [Module.Finite Ô S]
  {C : Type v} [Field C] [Algebra Ô C]
  {ϖ : Ô}
  {Φ : Finset (S →ₐ[Ô] C)}
-- given
  (hϖ0 : ϖ ≠ 0)
  (hinj : Function.Injective (algebraMap Ô C)) :
-- imply
  (Φ.card : ENat) ≤
    finsum fun 𝔓 : PrimeSpectrum S =>
      finsum (α := 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal)
        fun _ => (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ENat) := by
-- proof
  classical
  have hCϖ : algebraMap Ô C ϖ ≠ 0 := fun h => hϖ0 (hinj (h.trans (map_zero _).symm))
  let _ : IsNoetherianRing S := isNoetherian_of_tower Ô (inferInstance : IsNoetherian Ô S)
  set cond : PrimeSpectrum S → Prop :=
    fun 𝔓 => 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap Ô S ϖ ∉ 𝔓.asIdeal with hcond
  have hQfin : {𝔓 : PrimeSpectrum S | cond 𝔓}.Finite := by
    apply ((minimalPrimes.finite_of_isNoetherianRing S).preimage (fun a _ b _ h => PrimeSpectrum.ext h)).subset fun 𝔓 h => h.1
  change (Φ.card : ENat) ≤
    finsum fun 𝔓 => finsum (α := 𝔓 ∈ {𝔓 : PrimeSpectrum S | cond 𝔓})
      fun _ => (Module.finrank Ô (S ⧸ 𝔓.asIdeal) : ENat)
  rw [finsum_mem_eq_finite_toFinset_sum _ hQfin, ← Nat.cast_sum, Nat.cast_le]
  let κ : (S →ₐ[Ô] C) → PrimeSpectrum S := fun φ => ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩
  have hκcond : ∀ φ ∈ Φ, cond (κ φ) := by
    intro φ _
    refine ⟨ker_mem_minimalPrimes (φ := φ) hinj, ?_⟩
    change algebraMap Ô S ϖ ∉ RingHom.ker φ.toRingHom
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    apply hCϖ
  calc
    _ = ∑ 𝔓 ∈ Φ.image κ, (Φ.filter (fun φ => κ φ = 𝔓)).card := Finset.card_eq_sum_card_image κ Φ
    _ ≤ ∑ 𝔓 ∈ Φ.image κ, Module.finrank Ô (S ⧸ 𝔓.asIdeal) := by
      refine Finset.sum_le_sum fun 𝔓 h𝔓 => ?_
      obtain ⟨φ₀, hφ₀, rfl⟩ := Finset.mem_image.mp h𝔓
      have hfilt : Φ.filter (fun φ => κ φ = κ φ₀) =
          Φ.filter (fun φ => RingHom.ker φ.toRingHom = (κ φ₀).asIdeal) :=
        Finset.filter_congr fun φ _ => PrimeSpectrum.ext_iff
      rw [hfilt]
      let _ : (κ φ₀).asIdeal.IsPrime := (κ φ₀).isPrime
      apply card_filter_ker_eq_le (Φ := Φ) (𝔓 := (κ φ₀).asIdeal)
        (algebraMap_quotient_ker_injective (φ := φ₀) hinj)
    _ ≤ ∑ 𝔓 ∈ hQfin.toFinset, Module.finrank Ô (S ⧸ 𝔓.asIdeal) := by
      refine Finset.sum_le_sum_of_subset fun 𝔓 h𝔓 => ?_
      obtain ⟨φ₀, hφ₀, rfl⟩ := Finset.mem_image.mp h𝔓
      rw [Set.Finite.mem_toFinset]
      apply hκcond φ₀ hφ₀


-- created on 2026-10-13
