import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma isDomain_of_isPrincipal_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] (h : (IsLocalRing.maximalIdeal A).IsPrincipal) : IsDomain A := by
  classical
  obtain ⟨ϖ, hϖ⟩ := h
  replace hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖ
  have hpow : ∀ n : ℕ, IsLocalRing.maximalIdeal A ^ n = Ideal.span {ϖ ^ n} := fun n => by rw [hϖ, Ideal.span_singleton_pow]
  have hinf : ⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have key : ∀ a : A, a ≠ 0 → ∃ (n : ℕ) (u : A), IsUnit u ∧ a = u * ϖ ^ n := by
    intro a ha
    have hex : ∃ n : ℕ, a ∉ IsLocalRing.maximalIdeal A ^ n := by
      by_contra hcon
      push Not at hcon
      have hmem : a ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n := Ideal.mem_iInf.mpr hcon
      rw [hinf, Ideal.mem_bot] at hmem
      apply ha hmem
    have hN := Nat.find_spec hex
    have hNmin : ∀ m < Nat.find hex, a ∈ IsLocalRing.maximalIdeal A ^ m := fun m hm => by
      have := Nat.find_min hex hm
      simpa using this
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => ?_)
      rw [h0, pow_zero, Ideal.one_eq_top] at hN
      apply hN trivial
    have hak : a ∈ Ideal.span {ϖ ^ k} := by
      rw [← hpow]
      apply hNmin k (by omega)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hak
    refine ⟨k, c, ?_, rfl⟩
    by_contra hcu
    have hcm : c ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal c).mpr (mem_nonunits_iff.mpr hcu)
    rw [hϖ] at hcm
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hcm
    apply hN
    rw [hk, hpow]
    apply Ideal.mem_span_singleton'.mpr ⟨d, by ring⟩
  have hnz : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨n, u, hu, rfl⟩ := key a ha
    obtain ⟨m, v, hv, rfl⟩ := key b hb
    have hϖ0 : ϖ ^ (n + m) = 0 := by
      have : u * v * ϖ ^ (n + m) = 0 := by
        rw [← hab]
        ring
      apply (hu.mul hv).mul_right_eq_zero.mp this
    have hϖ0' : ϖ = 0 := IsNilpotent.eq_zero ⟨n + m, hϖ0⟩
    subst hϖ0'
    cases n
    ·
      cases m
      ·
        simp only [pow_zero, mul_one] at hab
        apply (hu.mul hv).ne_zero hab
      · apply hb (by simp)
    · apply ha (by simp)
  apply NoZeroDivisors.to_isDomain A
private lemma exists_notMem_isDomain_away {R : Type u} {Rp : Type v} [CommRing R] [CommRing Rp] [Algebra R Rp] [IsNoetherianRing R] [IsReduced R] (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime Rp P] [IsDomain Rp] : ∃ f : R, f ∉ P ∧ ∀ (Rf : Type u) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf], IsDomain Rf := by
  classical
  set Q₀ : Ideal R := RingHom.ker (algebraMap R Rp)
  have hQ₀prime : Q₀.IsPrime := RingHom.ker_isPrime _
  have hle : ∀ q : Ideal R, q.IsPrime → q ≤ P → Q₀ ≤ q := by
    intro q hq hqP r hr
    obtain ⟨⟨s, hs⟩, hsr⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl Rp r).mp hr
    have : s * r ∈ q := by simp [hsr]
    apply (hq.mem_or_mem this).resolve_left (fun h => hs (hqP h))
  have hQ₀P : Q₀ ≤ P := hle P ‹_› le_rfl
  have hpick : ∀ q ∈ minimalPrimes R, q ≠ Q₀ → ∃ g : R, g ∈ q ∧ g ∉ P := by
    intro q hq hne
    by_contra hcon
    push Not at hcon
    have hqP : q ≤ P := fun g hg => hcon g hg
    apply hne (le_antisymm (hq.2 ⟨hQ₀prime, bot_le⟩ (hle q hq.1.1 hqP)) (hle q hq.1.1 hqP))
  choose g hg using hpick
  let g' : Ideal R → R := fun q => if h : q ∈ minimalPrimes R ∧ q ≠ Q₀ then g q h.1 h.2 else 1
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let f : R := ∏ q ∈ hfin.toFinset, g' q
  have hfP : f ∉ P := by
    refine Finset.prod_induction g' (fun a => a ∉ P) (fun a b ha hb hab => ?_) ?_ ?_
    · apply (‹P.IsPrime›.mem_or_mem hab).elim ha hb
    · apply fun h1 => ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
    ·
      intro q hq
      if h : q ∈ minimalPrimes R ∧ q ≠ Q₀ then
        simp only [g', dite_eq_left h]
        apply (hg q h.1 h.2).2
      else
        simp only [g', dite_eq_right h]
        intro h1
        apply ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hfq : ∀ q ∈ minimalPrimes R, q ≠ Q₀ → f ∈ q := by
    intro q hq hne
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g' (hfin.mem_toFinset.mpr hq)
    change f = _ at hc
    rw [hc]
    refine q.mul_mem_right c ?_
    simp only [g', dite_eq_left (show q ∈ minimalPrimes R ∧ q ≠ Q₀ from ⟨hq, hne⟩)]
    apply (hg q hq hne).1
  have hfr : ∀ r ∈ Q₀, f * r = 0 := by
    intro r hr
    have hmem : f * r ∈ sInf (minimalPrimes R) := by
      refine Submodule.mem_sInf.mpr fun q hq => ?_
      if hne : q = Q₀ then
        subst hne
        apply Ideal.mul_mem_left _ f hr
      else
        apply Ideal.mul_mem_right r q (hfq q hq hne)
    have h0 : sInf (minimalPrimes R) = (⊥ : Ideal R) := by
      rw [minimalPrimes, Ideal.sInf_minimalPrimes]
      simp [nilradical] using nilradical_eq_zero R
    rw [h0] at hmem
    simpa using hmem
  have hfQ₀ : f ∉ Q₀ := fun h => hfP (hQ₀P h)
  refine ⟨f, hfP, fun Rf _ _ _ => ?_⟩
  have hpowQ : ∀ (m : Submonoid.powers f) (r : R), (m : R) * r ∈ Q₀ → r ∈ Q₀ := by
    intro m r hmr
    obtain ⟨m, hpowm⟩ := m
    obtain ⟨k, rfl⟩ := hpowm
    obtain h | h := hQ₀prime.mem_or_mem hmr
    · apply absurd (hQ₀prime.mem_of_pow_mem k h) hfQ₀
    · apply h
  let _ : Nontrivial Rf := by
    refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Rf (1 : R)).mp (by simpa using h10)
    have : (1 : R) ∈ Q₀ := hpowQ m 1 (by simp [hm])
    apply hQ₀prime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  let _ : NoZeroDivisors Rf := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨ra, sa, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) a
    obtain ⟨rb, sb, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) b
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hab
    obtain ⟨m, hm⟩ := hab
    have hab' : ra * rb ∈ Q₀ := hpowQ m _ (by simp [hm])
    obtain h | h := hQ₀prime.mem_or_mem hab'
    ·
      left
      apply (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨f, Submonoid.mem_powers f⟩, hfr ra h⟩
    ·
      right
      apply (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨f, Submonoid.mem_powers f⟩, hfr rb h⟩
  apply NoZeroDivisors.to_isDomain Rf
/--
[IsLocalization_AtPrime_exists_notMem_forall_isDomain_away_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalization_AtPrime_exists_notMem_forall_isDomain_away_of_isReduced.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
  (P : Ideal R) [P.IsPrime]
  (Rp : Type v) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp P] [IsDomain Rp] :
  -- imply
  ∃ f : R, f ∉ P ∧ ∀ (Rf : Type u) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf], IsDomain Rf :=
  exists_notMem_isDomain_away (Rp := Rp) P


-- created on 2026-10-20
