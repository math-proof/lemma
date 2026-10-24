import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isLocalRing_of_isAdicComplete {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hM : (Ideal.span {(p : 𝓞)}).IsMaximal) : IsLocalRing 𝓞 :=
  let _ := hM
  isLocalRing_of_isAdicComplete_maximal (Ideal.span {(p : 𝓞)})
private lemma isUnit_of_not_mem_span {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hM : (Ideal.span {(p : 𝓞)}).IsMaximal) {x : 𝓞} (hx : x ∉ Ideal.span {(p : 𝓞)}) : IsUnit x := by
  let _ := isLocalRing_of_isAdicComplete hM
  by_contra h
  apply hx ((IsLocalRing.eq_maximalIdeal hM).symm ▸ (IsLocalRing.mem_maximalIdeal x).2 h)
private lemma span_singleton_pow_eq {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} (n : ℕ) : (Ideal.span {(p : 𝓞)}) ^ n • (⊤ : Submodule 𝓞 𝓞) = Ideal.span {(p : 𝓞) ^ n} := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
private lemma exists_eq_pow_mul_of_ne_zero {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hM : (Ideal.span {(p : 𝓞)}).IsMaximal) {x : 𝓞} (hx : x ≠ 0) : ∃ (n : ℕ) (u : 𝓞), IsUnit u ∧ x = (p : 𝓞) ^ n * u := by
  classical
  have hex : ∃ n : ℕ, x ∉ Ideal.span {(p : 𝓞) ^ n} := by
    by_contra h
    push Not at h
    apply hx
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞) x fun n => ?_
    rw [SModEq.zero, span_singleton_pow_eq]
    apply h n
  let n₀ := Nat.find hex
  have hn₀ : x ∉ Ideal.span {(p : 𝓞) ^ n₀} := Nat.find_spec hex
  have hpos : n₀ ≠ 0 := by
    intro h0
    apply hn₀
    rw [h0, pow_zero, Ideal.span_singleton_one]
    apply Submodule.mem_top
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hxm : x ∈ Ideal.span {(p : 𝓞) ^ m} := by
    by_contra h
    refine Nat.find_min hex (m := m) ?_ h
    rw [show Nat.find hex = n₀ from rfl, hm]
    apply Nat.lt_succ_self m
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hxm
  refine ⟨m, u, ?_, by rw [← hu, mul_comm]⟩
  refine isUnit_of_not_mem_span hM fun hu' => hn₀ ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hu'
  rw [hm, ← hu, ← hc, Ideal.mem_span_singleton, pow_succ]
  exact ⟨c, by ring⟩
private lemma isDomain_of_isAdicComplete {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hM : (Ideal.span {(p : 𝓞)}).IsMaximal) : IsDomain 𝓞 := by
  let _ := isLocalRing_of_isAdicComplete hM
  let _ : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hM h.1
    obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero hM h.2
    apply (hu.mul hv).ne_zero (mem_nonZeroDivisors_iff_right.1 (Submonoid.pow_mem _ hp (m + n)) (u * v) _)
    rw [← hab]
    ring⟩
  apply NoZeroDivisors.to_isDomain
private lemma irreducible_natCast {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hM : (Ideal.span {(p : 𝓞)}).IsMaximal) : Irreducible (p : 𝓞) := by
  let _ := isLocalRing_of_isAdicComplete hM
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} := (IsLocalRing.eq_maximalIdeal hM).symm
  have hpmem : (p : 𝓞) ∈ IsLocalRing.maximalIdeal 𝓞 := hmax ▸ Ideal.mem_span_singleton_self _
  refine ⟨(IsLocalRing.mem_maximalIdeal _).1 hpmem, fun a b hab => ?_⟩
  by_contra h
  push Not at h
  have ha : a ∈ Ideal.span {(p : 𝓞)} := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h.1
  have hb : b ∈ Ideal.span {(p : 𝓞)} := hmax ▸ (IsLocalRing.mem_maximalIdeal b).2 h.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hb
  apply (IsLocalRing.mem_maximalIdeal _).1 hpmem (isUnit_iff_exists_inv.2 ⟨c * d, (sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 hp _ _)).symm⟩)
  have : (p : 𝓞) = (p : 𝓞) * (p : 𝓞) * (c * d) := by
    conv_lhs => rw [hab, ← hc, ← hd]
    ring
  calc
    _ = (p : 𝓞) - (p : 𝓞) * (p : 𝓞) * (c * d) := by ring
    _ = 0 := by rw [← this, sub_self]
private lemma isDiscreteValuationRing_of_isAdicComplete {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hM : (Ideal.span {(p : 𝓞)}).IsMaximal) : @IsDiscreteValuationRing 𝓞 _ (isDomain_of_isAdicComplete hp hM) := by
  let _ := isDomain_of_isAdicComplete hp hM
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨(p : 𝓞), irreducible_natCast hp hM, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hM hx
  exact ⟨n, (associated_mul_unit_right ((p : 𝓞) ^ n) u hu)⟩
/--
[IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal.lean)
-/
@[path]
private lemma main
  {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
  -- imply
  ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞), Irreducible (p : 𝓞) ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} := by
  -- proof
  let hD : IsDomain 𝓞 := isDomain_of_isAdicComplete hp ‹_›
  let hDVR : IsDiscreteValuationRing 𝓞 := isDiscreteValuationRing_of_isAdicComplete hp ‹_›
  exact ⟨hD, hDVR, irreducible_natCast hp ‹_›, (IsLocalRing.eq_maximalIdeal ‹_›).symm⟩


-- created on 2026-10-20
