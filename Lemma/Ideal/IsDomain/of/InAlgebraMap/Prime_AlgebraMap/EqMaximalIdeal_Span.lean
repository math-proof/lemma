import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


/--
[Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap.lean)
-/
@[path]
private lemma main
  {A B S : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [Algebra A B] [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B] [CommRing S] [Algebra B S] [IsLocalRing S]
  {ϖ : A} {𝔫 : Ideal B} [𝔫.IsMaximal] [IsLocalization.AtPrime S 𝔫]
-- given
  (hϖ : maximalIdeal A = Ideal.span {ϖ})
  (hprime : Prime (algebraMap A B ϖ))
  (hϖ𝔫 : algebraMap A B ϖ ∈ 𝔫) :
-- imply
  IsDomain S := by
-- proof
  classical
  have : Algebra.Smooth A B := {}
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔫.primeCompl S inferInstance
  let _ : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat B S := IsLocalization.flat S 𝔫.primeCompl
  have : Module.Flat A S := Module.Flat.trans A B S
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hϖ
    apply IsDiscreteValuationRing.not_isField A ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hϖ)
  set π : S := algebraMap B S (algebraMap A B ϖ) with hπ
  have hπA : ∀ s : S, ϖ • s = π * s := fun s => Algebra.smul_def ϖ s
  have hreg : ∀ s : S, π * s = 0 → s = 0 := by
    intro s hs
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) (mem_nonZeroDivisors_of_ne_zero hϖ0)
    apply this
    show ϖ • s = ϖ • (0 : S)
    rw [hπA, hs, hπA, mul_zero]
  have hregpow : ∀ (n : ℕ) (s : S), π ^ n * s = 0 → s = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs
      simp at hs
      apply hs
    | succ n ih =>
      intro s hs
      rw [pow_succ, mul_assoc] at hs
      apply hreg _ (ih _ hs)
  have hπ𝔪 : π ∈ maximalIdeal S := by
    rw [hπ]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔫 _).mpr hϖ𝔫
  have hπ0 : π ≠ 0 := by
    intro h0
    have h1 : (1 : S) = 0 := by
      apply hreg 1
      rw [h0, zero_mul]
    refine one_ne_zero h1
  have hπprime : Prime π := by
    have hdisj : Disjoint (𝔫.primeCompl : Set B) (Ideal.span {algebraMap A B ϖ} : Set B) := by
      rw [Set.disjoint_left]
      intro b hb hb'
      apply hb ((Ideal.span_singleton_le_iff_mem _).mpr hϖ𝔫 hb')
    have : (Ideal.span {algebraMap A B ϖ}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    have hP : ((Ideal.span {algebraMap A B ϖ}).map (algebraMap B S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint 𝔫.primeCompl S _ inferInstance hdisj
    rw [Ideal.map_span, Set.image_singleton] at hP
    apply (Ideal.span_singleton_prime hπ0).mp hP
  have hkrull : ⨅ n : ℕ, (Ideal.span {π}) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (fun h => hπprime.not_isUnit (Ideal.span_singleton_eq_top.mp h))
  have hdecomp : ∀ a : S, a ≠ 0 → ∃ (m : ℕ) (a' : S), a = π ^ m * a' ∧ ¬ π ∣ a' := by
    intro a ha
    have hex : ∃ n : ℕ, ¬ π ^ n ∣ a := by
      by_contra hall
      push Not at hall
      apply ha
      have : a ∈ ⨅ n : ℕ, (Ideal.span {π}) ^ n := by
        rw [Submodule.mem_iInf]
        intro n
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        apply hall n
      rwa [hkrull, Submodule.mem_bot] at this
    let k := Nat.find hex
    have hk : ¬ π ^ k ∣ a := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h
      apply hk
      rw [h, pow_zero]
      apply one_dvd
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hdvd : π ^ m ∣ a := by
      have := Nat.find_min hex (show m < k by omega)
      push Not at this
      apply this
    obtain ⟨a', ha'⟩ := hdvd
    refine ⟨m, a', ha', fun hd => hk ?_⟩
    rw [hm, pow_succ, ha']
    apply mul_dvd_mul_left _ hd
  have : NoZeroDivisors S := ⟨fun {a b} hab => by
    by_contra hne
    push Not at hne
    obtain ⟨ha, hb⟩ := hne
    obtain ⟨m, a', rfl, ha'⟩ := hdecomp a ha
    obtain ⟨k, b', rfl, hb'⟩ := hdecomp b hb
    have : π ^ (m + k) * (a' * b') = 0 := by
      rw [← hab]
      ring
    have h0 := hregpow _ _ this
    have hdiv : π ∣ a' * b' := by
      rw [h0]
      apply dvd_zero
    obtain h | h := hπprime.dvd_or_dvd hdiv
    · apply ha' h
    · apply hb' h⟩
  apply NoZeroDivisors.to_isDomain


-- created on 2026-10-13
