import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {𝓞 : Type u} [CommRing 𝓞] {ϖ : 𝓞}
private lemma isLocalRing_of_isAdicComplete [IsAdicComplete (Ideal.span {ϖ}) 𝓞]
    (hM : (Ideal.span {ϖ}).IsMaximal) : IsLocalRing 𝓞 :=
  let _ := hM
  isLocalRing_of_isAdicComplete_maximal (Ideal.span {ϖ})
private lemma isUnit_of_not_mem_span [IsAdicComplete (Ideal.span {ϖ}) 𝓞]
    (hM : (Ideal.span {ϖ}).IsMaximal) {x : 𝓞}
    (hx : x ∉ Ideal.span {ϖ}) : IsUnit x := by
  let _ := isLocalRing_of_isAdicComplete hM
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (hM)).symm
  by_contra h
  exact hx (hmax ▸ (IsLocalRing.mem_maximalIdeal x).2 h)
private lemma span_singleton_pow_eq (n : ℕ) :
    (Ideal.span {ϖ}) ^ n • (⊤ : Submodule 𝓞 𝓞) = Ideal.span {ϖ ^ n} := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
private lemma exists_eq_pow_mul_of_ne_zero [IsAdicComplete (Ideal.span {ϖ}) 𝓞]
    (hM : (Ideal.span {ϖ}).IsMaximal) {x : 𝓞} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝓞), IsUnit u ∧ x = ϖ ^ n * u := by
  classical
  have hex : ∃ n : ℕ, x ∉ Ideal.span {ϖ ^ n} := by
    by_contra h
    push Not at h
    apply hx
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) 𝓞) x fun n => ?_
    rw [SModEq.zero, span_singleton_pow_eq]
    exact h n
  let n₀ := Nat.find hex
  have hn₀ : x ∉ Ideal.span {ϖ ^ n₀} := Nat.find_spec hex
  have hpos : n₀ ≠ 0 := by
    intro h0
    apply hn₀
    rw [h0, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hxm : x ∈ Ideal.span {ϖ ^ m} := by
    by_contra h
    have := Nat.find_min hex (m := m) (by rw [show Nat.find hex = n₀ from rfl, hm]; exact Nat.lt_succ_self m)
    exact this h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hxm
  refine ⟨m, u, ?_, by rw [← hu, mul_comm]⟩
  refine isUnit_of_not_mem_span hM fun hu' => hn₀ ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hu'
  rw [hm, ← hu, ← hc, Ideal.mem_span_singleton, pow_succ]
  exact ⟨c, by ring⟩
private lemma isDomain_of_isAdicComplete [IsAdicComplete (Ideal.span {ϖ}) 𝓞]
    (hp : ϖ ∈ nonZeroDivisors 𝓞)
    (hM : (Ideal.span {ϖ}).IsMaximal) : IsDomain 𝓞 := by
  let _ := isLocalRing_of_isAdicComplete hM
  let _ : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hM h.1
    obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero hM h.2
    have h1 : u * v * ϖ ^ (m + n) = 0 := by rw [← hab]; ring
    have h2 : u * v = 0 := mem_nonZeroDivisors_iff_right.1 (Submonoid.pow_mem _ hp (m + n)) _ h1
    exact (hu.mul hv).ne_zero h2⟩
  exact NoZeroDivisors.to_isDomain 𝓞
private lemma irreducible_gen [IsAdicComplete (Ideal.span {ϖ}) 𝓞]
    (hp : ϖ ∈ nonZeroDivisors 𝓞)
    (hM : (Ideal.span {ϖ}).IsMaximal) : Irreducible ϖ := by
  let _ := isLocalRing_of_isAdicComplete hM
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (hM)).symm
  have hpmem : ϖ ∈ IsLocalRing.maximalIdeal 𝓞 := hmax ▸ Ideal.mem_span_singleton_self _
  refine ⟨(IsLocalRing.mem_maximalIdeal _).1 hpmem, fun a b hab => ?_⟩
  by_contra h
  push Not at h
  have ha : a ∈ Ideal.span {ϖ} := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h.1
  have hb : b ∈ Ideal.span {ϖ} := hmax ▸ (IsLocalRing.mem_maximalIdeal b).2 h.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hb
  have h1 : (1 - ϖ * (c * d)) * ϖ = 0 := by
    have : ϖ = ϖ * ϖ * (c * d) := by
      conv_lhs => rw [hab, ← hc, ← hd]
      ring
    calc (1 - ϖ * (c * d)) * ϖ = ϖ - ϖ * ϖ * (c * d) := by ring
      _ = 0 := by rw [← this, sub_self]
  have h2 : 1 - ϖ * (c * d) = 0 := mem_nonZeroDivisors_iff_right.1 hp _ h1
  have hunit : IsUnit ϖ := isUnit_iff_exists_inv.2 ⟨c * d, (sub_eq_zero.1 h2).symm⟩
  exact (IsLocalRing.mem_maximalIdeal _).1 hpmem hunit
private lemma isDiscreteValuationRing_of_isAdicComplete [IsAdicComplete (Ideal.span {ϖ}) 𝓞]
    (hp : ϖ ∈ nonZeroDivisors 𝓞)
    (hM : (Ideal.span {ϖ}).IsMaximal) :
    @IsDiscreteValuationRing 𝓞 _ (isDomain_of_isAdicComplete hp hM) := by
  let _ := isDomain_of_isAdicComplete hp hM
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ϖ, irreducible_gen hp hM, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hM hx
  exact ⟨n, (associated_mul_unit_right (ϖ ^ n) u hu)⟩
/--
[IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal.lean)
-/
@[path]
private lemma main
    {𝓞 : Type u} [CommRing 𝓞] (ϖ : 𝓞) (hp : ϖ ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) 𝓞] :
    ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞),
      Irreducible ϖ ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {ϖ} := by
  let hD : IsDomain 𝓞 := isDomain_of_isAdicComplete hp ‹_›
  let hDVR : IsDiscreteValuationRing 𝓞 := isDiscreteValuationRing_of_isAdicComplete hp ‹_›
  exact ⟨hD, hDVR, irreducible_gen hp ‹_›, (IsLocalRing.eq_maximalIdeal ‹_›).symm⟩

-- created on 2026-10-20
