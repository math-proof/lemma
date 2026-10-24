import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma smul_sub_mem_of_inertia
  {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  {A : ValuationSubring L}
  (τ : ↥(A.decompositionSubgroup K)) (hτ : τ ∈ A.inertiaSubgroup K) (a : ↥A) :
  τ • a - a ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, IsLocalRing.ResidueField.residue_smul, sub_eq_zero]
  refine DFunLike.congr_fun (MonoidHom.mem_ker.mp hτ) (IsLocalRing.residue ↥A a)

private lemma coe_smul
  {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  {A : ValuationSubring L}
  (τ : ↥(A.decompositionSubgroup K)) (a : ↥A) :
  ((τ • a : ↥A) : L) = (τ : L ≃ₐ[K] L) (a : L) := rfl

private lemma exists_smul_sub_eq_mul
  {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  {A : ValuationSubring L} [IsDiscreteValuationRing ↥A]
  (τ : ↥(A.decompositionSubgroup K)) (hτ₀ : τ ∈ A.inertiaSubgroup K)
  (hτ : ∀ ϖ : ↥A, Irreducible ϖ → (τ • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2)
  (a : ↥A) :
  ∃ c ∈ IsLocalRing.maximalIdeal ↥A, τ • a - a = c * a := by
  classical
  if ha : a = 0 then
    refine ⟨0, Ideal.zero_mem _, by rw [ha, smul_zero, sub_zero, mul_zero]⟩
  else
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A
    obtain ⟨n, w, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    subst hn
    have hspan : IsLocalRing.maximalIdeal ↥A = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    have h2 := hτ ϖ hϖ
    rw [pow_two, hspan, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton'] at h2
    obtain ⟨d, hd⟩ := h2
    have hτϖ : τ • ϖ = (1 + d * ϖ) * ϖ := by
      rw [show τ • ϖ = ϖ + (τ • ϖ - ϖ) by ring, ← hd]
      ring
    have hm : d * ϖ ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [hspan]
      refine Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ϖ)
    set m := d * ϖ
    have hpow : (1 + m) ^ n - 1 ∈ IsLocalRing.maximalIdeal ↥A := by
      have hdvd : (1 + m) - 1 ∣ (1 + m) ^ n - 1 ^ n := sub_dvd_pow_sub_pow (1 + m) 1 n
      rw [add_sub_cancel_left, one_pow] at hdvd
      refine Ideal.mem_of_dvd _ hdvd hm
    have hw : τ • (w : ↥A) - w ∈ IsLocalRing.maximalIdeal ↥A := smul_sub_mem_of_inertia τ hτ₀ w
    refine ⟨((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * (w⁻¹ : Units ↥A), ?_, ?_⟩
    · refine Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_left _ _ hpow))
    ·
      rw [smul_mul', smul_pow', hτϖ, mul_pow]
      have hu : ((w⁻¹ : Units ↥A) : ↥A) * (w : ↥A) = 1 := Units.inv_mul w
      calc
        _ = ((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * ϖ ^ n := by
          ring
        _ = ((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * (((w⁻¹ : Units ↥A) : ↥A) * w) * ϖ ^ n := by
          rw [hu, mul_one]
        _ = ((τ • (w : ↥A) - w) * (1 + m) ^ n + w * ((1 + m) ^ n - 1)) * ((w⁻¹ : Units ↥A) : ↥A) * ((w : ↥A) * ϖ ^ n) := by
          ring

private lemma isUnit_one_add
  {L : Type v} [Field L] {A : ValuationSubring L}
  {c : ↥A} (hc : c ∈ IsLocalRing.maximalIdeal ↥A) : IsUnit (1 + c) := by
  by_contra h
  have h1 : (1 + c : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have := Ideal.sub_mem _ h1 hc
    rw [add_sub_cancel_right] at this
    refine this
  refine (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

private lemma exists_apply_sub_eq_mul
  {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  {A : ValuationSubring L} [IsDiscreteValuationRing ↥A]
  (τ : ↥(A.decompositionSubgroup K)) (hτ₀ : τ ∈ A.inertiaSubgroup K)
  (hτ : ∀ ϖ : ↥A, Irreducible ϖ → (τ • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2)
  (x : L) :
  ∃ m ∈ IsLocalRing.maximalIdeal ↥A, (τ : L ≃ₐ[K] L) x - x = (m : L) * x := by
  classical
  obtain ⟨a, b, hb, hxab⟩ : ∃ a b : ↥A, (b : L) ≠ 0 ∧ x = (a : L) / (b : L) := by
    if hx0 : x = 0 then
      refine ⟨0, 1, by simp, by simp [hx0]⟩
    else
      refine (A.mem_or_inv_mem x).elim ?_ ?_
      ·
        intro hx
        refine ⟨⟨x, hx⟩, 1, by simp, by simp⟩
      ·
        intro hx
        refine ⟨1, ⟨x⁻¹, hx⟩, by simpa using hx0, by simp⟩
  subst hxab
  obtain ⟨c₁, hc₁, h₁⟩ := exists_smul_sub_eq_mul τ hτ₀ hτ a
  obtain ⟨c₂, hc₂, h₂⟩ := exists_smul_sub_eq_mul τ hτ₀ hτ b
  have hτa : τ • a = (1 + c₁) * a := by
    rw [add_mul, one_mul, ← h₁]
    ring
  have hτb : τ • b = (1 + c₂) * b := by
    rw [add_mul, one_mul, ← h₂]
    ring
  have ha' : (τ : L ≃ₐ[K] L) (a : L) = ((1 + c₁ : ↥A) : L) * a := by
    rw [← coe_smul, hτa, MulMemClass.coe_mul]
  have hb' : (τ : L ≃ₐ[K] L) (b : L) = ((1 + c₂ : ↥A) : L) * b := by
    rw [← coe_smul, hτb, MulMemClass.coe_mul]
  obtain ⟨e, he⟩ := (isUnit_one_add hc₂).exists_right_inv
  have hmul : (1 + (c₂ : L)) * (e : L) = 1 := by
    have := congrArg (fun z : ↥A => (z : L)) he
    push_cast at this
    refine this
  have hne : (1 + (c₂ : L)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    refine zero_ne_one hmul
  have he' : ((e : ↥A) : L) = (1 + (c₂ : L))⁻¹ := eq_inv_of_mul_eq_one_right hmul
  refine ⟨(c₁ - c₂) * e, Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hc₁ hc₂), ?_⟩
  rw [map_div₀, ha', hb']
  push_cast
  rw [he']
  field_simp
  ring

/--
[ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_isPGroup_of_forall_mem_iff_smul_sub_mem_sq.lean)
-/
@[path]
private lemma main
  (K : Type u) [Field K]
  {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (A : ValuationSubring L) [IsDiscreteValuationRing ↥A]
  (p : ℕ) [Fact p.Prime] (hp : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)
  (Pw : Subgroup ↥(A.inertiaSubgroup K))
  (hPw : ∀ σ : ↥(A.inertiaSubgroup K), σ ∈ Pw ↔ ∀ ϖ : ↥A, Irreducible ϖ → ((σ : ↥(A.decompositionSubgroup K)) • ϖ - ϖ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ^ 2) :
  -- imply
  IsPGroup p ↥Pw := by
  -- proof
  classical
  let _ : Fintype ↥Pw := Fintype.ofFinite ↥Pw
  suffices key : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Fintype.card ↥Pw → ℓ = p by
    rw [IsPGroup.iff_card, ← Fintype.card_eq_nat_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Fintype.card_ne_zero (fun hd hdvd => key _ hd hdvd)⟩
  intro ℓ hℓ hℓdvd
  by_contra hℓp
  let _ : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card ℓ hℓdvd
  let ι : ↥Pw → (L ≃ₐ[K] L) := fun h => (((h : ↥(A.inertiaSubgroup K)) : ↥(A.decompositionSubgroup K)) : L ≃ₐ[K] L)
  have hι_pow : ∀ (h : ↥Pw) (i : ℕ), ι (h ^ i) = ι h ^ i := fun h i => rfl
  have hι_one : ι 1 = 1 := rfl
  have hι_inj : Function.Injective ι := fun h h' hh => Subtype.ext (Subtype.ext (Subtype.ext hh))
  set σ := ι g with hσ
  have hσℓ : σ ^ ℓ = 1 := by
    rw [hσ, ← hι_pow, ← hg, pow_orderOf_eq_one, hι_one]
  have hmove : ∀ (i : ℕ) (x : L), ∃ m ∈ IsLocalRing.maximalIdeal ↥A, (σ ^ i) x - x = (m : L) * x := by
    intro i x
    have hmem : ((g ^ i : ↥Pw) : ↥(A.inertiaSubgroup K)) ∈ Pw := (g ^ i).2
    obtain ⟨m, hm, h⟩ := exists_apply_sub_eq_mul (K := K)
      (((g ^ i : ↥Pw) : ↥(A.inertiaSubgroup K)) : ↥(A.decompositionSubgroup K))
      ((g ^ i : ↥Pw) : ↥(A.inertiaSubgroup K)).2 ((hPw _).mp hmem) x
    refine ⟨m, hm, ?_⟩
    rw [hσ, ← hι_pow]
    refine h
  have hℓunit : IsUnit ((ℓ : ℕ) : ↥A) := by
    by_contra h
    have hℓmem : ((ℓ : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr h
    have hcop : IsCoprime ((p : ℤ) : ↥A) ((ℓ : ℤ) : ↥A) := by
      refine (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes Fact.out hℓ).mpr (Ne.symm hℓp))).map (Int.castRingHom ↥A)
    obtain ⟨u, v, huv⟩ := hcop
    push_cast at huv
    have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← huv]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hℓmem)
    refine (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  let T : L →ₗ[K] L := ∑ i ∈ Finset.range ℓ, (σ ^ i).toLinearMap
  have hT : ∀ x : L, T x = ∑ i ∈ Finset.range ℓ, (σ ^ i) x := by
    intro x
    simp [T]
  have hTunit : ∀ x : L, ∃ u : ↥A, IsUnit u ∧ T x = (u : L) * x := by
    intro x
    choose m hm hmx using fun i => hmove i x
    have hsum : ∑ i ∈ Finset.range ℓ, m i ∈ IsLocalRing.maximalIdeal ↥A := Ideal.sum_mem _ fun i _ => hm i
    refine ⟨(ℓ : ↥A) + ∑ i ∈ Finset.range ℓ, m i, ?_, ?_⟩
    ·
      by_contra hnu
      have hmem : (ℓ : ↥A) + ∑ i ∈ Finset.range ℓ, m i ∈ IsLocalRing.maximalIdeal ↥A :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have : ((ℓ : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        have := Ideal.sub_mem _ hmem hsum
        rw [add_sub_cancel_right] at this
        refine this
      refine (IsLocalRing.mem_maximalIdeal _).mp this hℓunit
    ·
      rw [hT]
      have : ∀ i ∈ Finset.range ℓ, (σ ^ i) x = x + (m i : L) * x := fun i _ => by
        rw [← hmx i]
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_mul]
      push_cast
      ring
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨u, hu, hux⟩ := hTunit x
    rw [hux] at hx
    refine (mul_eq_zero.mp hx).elim ?_ ?_
    ·
      intro h
      exfalso
      apply hu.ne_zero
      exact_mod_cast h
    ·
      intro h
      refine h
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  have hσT : ∀ x : L, σ (T x) = T x := by
    intro x
    rw [hT, map_sum]
    have h1 : ∑ i ∈ Finset.range ℓ, σ ((σ ^ i) x) = ∑ i ∈ Finset.range ℓ, (σ ^ (i + 1)) x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ']
      rfl
    rw [h1]
    have h2 : ∑ i ∈ Finset.range (ℓ + 1), (σ ^ i) x = ∑ i ∈ Finset.range ℓ, (σ ^ i) x + (σ ^ ℓ) x :=
      Finset.sum_range_succ _ _
    have h3 : ∑ i ∈ Finset.range (ℓ + 1), (σ ^ i) x = ∑ i ∈ Finset.range ℓ, (σ ^ (i + 1)) x + (σ ^ 0) x :=
      Finset.sum_range_succ' _ _
    have key := h3.symm.trans h2
    rw [pow_zero, hσℓ] at key
    refine add_right_cancel key
  have hσ1 : σ = 1 := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, hx⟩ := hTsurj y
    subst hx
    refine hσT x
  have hg1 : g = 1 := hι_inj (by rw [← hσ, hσ1, hι_one])
  rw [hg1, orderOf_one] at hg
  refine hℓ.one_lt.ne hg


-- created on 2026-10-21
