import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma pin_unique
  {A₀ R : Type} [CommRing A₀] [CommRing R] [Algebra A₀ R]
  {ℓ : ℕ}
  {ω : A₀}
  {ξ : R}
  {I : Ideal R}
  {i j : ℕ}
  -- given
  (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
  (hI : I ≠ ⊤)
  (hi : i < ℓ)
  (hj : j < ℓ)
  (hiI : ξ - algebraMap A₀ R (ω ^ i) ∈ I)
  (hjI : ξ - algebraMap A₀ R (ω ^ j) ∈ I) :
  -- imply
  i = j := by
  -- proof
  by_contra hij
  apply hI
  apply I.eq_top_of_isUnit_mem _ ((hωu i j hi hj hij).map _)
  have := I.sub_mem hjI hiI
  rwa [sub_sub_sub_cancel_left, ← map_sub] at this

private lemma exists_pin_mem
  {A₀ R : Type} [CommRing A₀] [CommRing R] [Algebra A₀ R]
  {ℓ : ℕ} [Fact ℓ.Prime]
  {𝔭 : Ideal R} [𝔭.IsPrime]
  {ω : A₀}
  {ξ : R}
  -- given
  (hℓ : IsUnit ((ℓ : ℕ) : A₀))
  (hω : IsPrimitiveRoot ω ℓ)
  (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
  (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A₀) = 0) :
  -- imply
  ∃ j : ℕ, (1 ≤ j ∧ j < ℓ) ∧ ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭 := by
  -- proof
  have hℓp : ℓ.Prime := Fact.out
  have hℓpos : 0 < ℓ := hℓp.pos
  let _ : NeZero ℓ := ⟨hℓp.ne_zero⟩
  let π : R →ₐ[A₀] R ⧸ 𝔭 := Ideal.Quotient.mkₐ A₀ 𝔭
  let φ : A₀ →+* R ⧸ 𝔭 := (π : R →+* R ⧸ 𝔭).comp (algebraMap A₀ R)
  have hφ : ∀ a, φ a = π (algebraMap A₀ R a) := fun _ => rfl
  have hne : ∀ l : ℕ, 0 < l → l < ℓ → (φ ω) ^ l ≠ 1 := by
    intro l hl hlt h1
    have hu := (hωu l 0 hlt hℓpos (by omega)).map φ
    rw [map_sub, map_pow, map_pow, pow_zero, h1, sub_self] at hu
    apply not_isUnit_zero hu
  have hω' : IsPrimitiveRoot (φ ω) ℓ := Iff.mpr (IsPrimitiveRoot.iff hℓpos) ⟨by rw [← map_pow, hω.pow_eq_one, map_one], hne⟩
  have hξℓ : ξ ^ ℓ = 1 := by
    have h := congrArg (Polynomial.aeval ξ) (Polynomial.cyclotomic_prime_mul_X_sub_one A₀ ℓ)
    simp only [map_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, hξ, zero_mul] at h
    apply Iff.mp sub_eq_zero h.symm
  have hξℓ' : (π ξ) ^ ℓ = 1 := by
    rw [← map_pow, hξℓ, map_one]
  obtain ⟨i, hi, hωi⟩ := hω'.eq_pow_of_pow_eq_one hξℓ'
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hωi
    have h := congrArg π hξ
    rw [map_zero, ← Polynomial.aeval_algHom_apply, ← hωi, show (1 : R ⧸ 𝔭) = algebraMap A₀ (R ⧸ 𝔭) 1 from (map_one _).symm, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Polynomial.eval_one_cyclotomic_prime] at h
    have hu := hℓ.map (algebraMap A₀ (R ⧸ 𝔭))
    rw [map_natCast] at hu
    rw [map_natCast] at h
    apply not_isUnit_zero (h ▸ hu)
  refine ⟨i, ⟨by omega, hi⟩, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  change π ξ = π (algebraMap A₀ R (ω ^ i))
  rw [← hφ, map_pow, hωi]

/--
[Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero.lean)
-/
@[path]
private lemma main
  {A₀ R : Type} [CommRing A₀] [CommRing R] [Algebra A₀ R]
  {ℓ : ℕ} [Fact ℓ.Prime]
  {ω : A₀}
  {ξ : R}
  -- given
  (hℓ : IsUnit ((ℓ : ℕ) : A₀))
  (hω : IsPrimitiveRoot ω ℓ)
  (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
  (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A₀) = 0) :
  -- imply
  (∀ 𝔭 ∈ (⊥ : Ideal R).minimalPrimes, ∃! j : ℕ, (1 ≤ j ∧ j < ℓ) ∧ ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭) ∧ (∀ j : ℕ, 1 ≤ j → j < ℓ → IsDomain (R ⧸ Ideal.span {ξ - algebraMap A₀ R (ω ^ j)}) → Ideal.span {ξ - algebraMap A₀ R (ω ^ j)} ∈ (⊥ : Ideal R).minimalPrimes ∧ ∀ 𝔭 ∈ (⊥ : Ideal R).minimalPrimes, ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭 → 𝔭 = Ideal.span {ξ - algebraMap A₀ R (ω ^ j)}) := by
  -- proof
  constructor
  ·
    intro 𝔭 h𝔭
    let _ : 𝔭.IsPrime := h𝔭.1.1
    obtain ⟨j, hj, hjm⟩ := exists_pin_mem hℓ hω hωu hξ
    refine ⟨j, ⟨hj, hjm⟩, fun i ⟨hi, him⟩ => ?_⟩
    apply pin_unique hωu (Ideal.IsPrime.ne_top ‹_›) hi.2 hj.2 him hjm
  ·
    intro j hj1 hjℓ hdom
    set I : Ideal R := Ideal.span {ξ - algebraMap A₀ R (ω ^ j)} with hIdef
    let hIp : I.IsPrime := Iff.mp (Ideal.Quotient.isDomain_iff_prime I) hdom
    have hξI : ξ - algebraMap A₀ R (ω ^ j) ∈ I := Ideal.subset_span (Set.mem_singleton _)
    constructor
    ·
      refine ⟨⟨hIp, bot_le⟩, ?_⟩
      rintro q ⟨hq, -⟩ hqI
      let _ := hq
      obtain ⟨𝔭, h𝔭, h𝔭q⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ q)
      let _ : 𝔭.IsPrime := h𝔭.1.1
      obtain ⟨i, hi, him⟩ := exists_pin_mem hℓ hω hωu hξ
      have hij : i = j := pin_unique hωu hIp.ne_top hi.2 hjℓ (hqI (h𝔭q him)) hξI
      subst hij
      rw [hIdef, Ideal.span_singleton_le_iff_mem]
      apply h𝔭q him
    ·
      intro 𝔭 h𝔭 hm
      have hI𝔭 : I ≤ 𝔭 := by
        rw [hIdef, Ideal.span_singleton_le_iff_mem]
        apply hm
      apply le_antisymm (h𝔭.2 ⟨hIp, bot_le⟩ hI𝔭) hI𝔭


-- created on 2026-10-21
