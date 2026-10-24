import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_LocalConditions
import Lemma.Int.P2MUtil

open IsLocalRing Module

/--
[GaloisRepAdic_detIsCyclotomic_of_jointly_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_detIsCyclotomic_of_jointly_injective.lean)
-/

private theorem det_baseChangeAlong_apply {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong φ hφ).ρ σ) = φ (LinearMap.det (ρ.ρ σ)) := by
  letI := φ.toAlgebra
  exact LinearMap.det_baseChange (ρ.ρ σ)

private theorem exists_apply_eq_pow_of_pow_eq_one (n : ℕ) (hn : n ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a := by
  haveI : NeZero n := ⟨hn⟩
  refine ⟨(modularCyclotomicCharacter.toFun n
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).val, fun μ hμ => ?_⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hμ
    exact zero_ne_one hμ
  have hmem : Units.mk0 μ hμ0 ∈ rootsOfUnity n (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity']
    exact hμ
  have h := modularCyclotomicCharacter.toFun_spec'
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem
  simpa using h

private theorem modEq_of_forall_apply_eq_pow {n : ℕ} (hn : n ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {a a' : ℕ}
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a)
    (ha' : ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a') : a ≡ a' [MOD n] := by
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n
  have h : ζ ^ a = ζ ^ a' := by rw [← ha ζ hζ.pow_eq_one, ha' ζ hζ.pow_eq_one]
  have hmod := (hζ.isOfFinOrder hn).pow_eq_pow_iff_modEq.mp h
  rwa [← hζ.eq_orderOf] at hmod

private theorem natCast_sub_natCast_mem_span {R : Type} [CommRing R] {n a b : ℕ}
    (h : a ≡ b [MOD n]) : (b : R) - (a : R) ∈ Ideal.span {(n : R)} := by
  rw [Ideal.mem_span_singleton]
  simpa only [eq_intCast, Int.cast_natCast, Int.cast_sub] using map_dvd (Int.castRingHom R) h.dvd

private theorem sub_natCast_mem_span_of_jointly_injective {P A B : Type} [CommRing P]
    [CommRing A] [CommRing B] (πA : P →+* A) (πB : P →+* B)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0)
    {p : ℕ} (hnA : IsNilpotent (p : A)) (hnB : IsNilpotent (p : B))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (d : P)
    (hA : ∀ n a : ℕ, (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
      πA d - (a : A) ∈ Ideal.span {((p ^ n : ℕ) : A)})
    (hB : ∀ n a : ℕ, (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
      πB d - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)})
    (n a : ℕ) (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) :
    d - (a : P) ∈ Ideal.span {((p ^ n : ℕ) : P)} := by

  have exact_of_vanish : ∀ k a' : ℕ, ((p ^ k : ℕ) : A) = 0 → ((p ^ k : ℕ) : B) = 0 →
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 → σ μ = μ ^ a') → d - (a' : P) = 0 := by
    intro k a' hkA hkB ha'
    have h1 := hA k a' ha'
    have h2 := hB k a' ha'
    rw [hkA, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at h1
    rw [hkB, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at h2
    exact hinj _ (by rw [map_sub, map_natCast]; exact h1) (by rw [map_sub, map_natCast]; exact h2)
  by_cases hp0 : p = 0
  · subst hp0
    cases n with
    | zero => rw [pow_zero, Nat.cast_one, Ideal.span_singleton_one]; exact Submodule.mem_top
    | succ n =>
      rw [exact_of_vanish (n + 1) a (by rw [zero_pow n.succ_ne_zero, Nat.cast_zero])
        (by rw [zero_pow n.succ_ne_zero, Nat.cast_zero]) ha]
      exact Submodule.zero_mem _
  · obtain ⟨NA, hNA⟩ := hnA
    obtain ⟨NB, hNB⟩ := hnB
    obtain ⟨aK, haK⟩ :=
      exists_apply_eq_pow_of_pow_eq_one (p ^ (n + (NA + NB))) (pow_ne_zero _ hp0) σ
    have hd : d - (aK : P) = 0 :=
      exact_of_vanish (n + (NA + NB)) aK
        (by rw [Nat.cast_pow]; exact pow_eq_zero_of_le (by omega) hNA)
        (by rw [Nat.cast_pow]; exact pow_eq_zero_of_le (by omega) hNB) haK
    have hmod : a ≡ aK [MOD p ^ n] :=
      modEq_of_forall_apply_eq_pow (pow_ne_zero n hp0) σ ha fun μ hμ =>
        haK μ (by rw [pow_add, pow_mul, hμ, one_pow])
    rw [show d - (a : P) = d - (aK : P) + ((aK : P) - (a : P)) by ring, hd, zero_add]
    exact natCast_sub_natCast_mem_span hmod
@[path]
private lemma main
  {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  {πA : P →+* A}
  {πB : P →+* B}
  {ρ : GaloisRepAdic P}
  {p : ℕ}
-- given
  (hπA : IsLocalHom πA)
  (hπB : IsLocalHom πB)
  (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0)
  (hnA : IsNilpotent (p : A))
  (hnB : IsNilpotent (p : B))
  (hA : (ρ.baseChangeAlong πA hπA).DetIsCyclotomic p)
  (hB : (ρ.baseChangeAlong πB hπB).DetIsCyclotomic p) :
-- imply
  ρ.DetIsCyclotomic p := by
-- proof
  refine ⟨?_, fun n σ a ha => ?_⟩
  · have h0 := hA.1
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0 ⊢
    exact fun hu => h0 (by simpa only [map_natCast] using hu.map πA)
  · exact sub_natCast_mem_span_of_jointly_injective πA πB hinj hnA hnB σ
      (LinearMap.det (ρ.ρ σ))
      (fun k a' ha' => by
        simpa only [det_baseChangeAlong_apply] using hA.2 k σ a' ha')
      (fun k a' ha' => by
        simpa only [det_baseChangeAlong_apply] using hB.2 k σ a' ha')
      n a ha


-- created on 2026-10-23
