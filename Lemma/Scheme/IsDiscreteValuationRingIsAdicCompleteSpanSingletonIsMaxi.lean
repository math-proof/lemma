import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsDiscreteValuationRing_of_isAdicComplete_span_singleton_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_of_isAdicComplete_span_singleton_of_isMaximal.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
  (hc : IsAdicComplete (Ideal.span {ϖ}) R) (hm : (Ideal.span {ϖ}).IsMaximal) :
  -- imply
  IsDiscreteValuationRing R := by
  -- proof
  classical
  let _ := hc
  set I : Ideal R := Ideal.span {ϖ} with hI
  have hunit : ∀ u : R, u ∉ I → IsUnit u := by
    intro u hu
    obtain ⟨y, i, hi, hyi⟩ := hm.exists_inv hu
    have hjac : i ∈ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I hi
    have h1 : IsUnit (i * (-1) + 1) := (Ideal.mem_jacobson_bot.1 hjac) (-1)
    have h2 : y * u = i * (-1) + 1 := by linear_combination hyi
    refine isUnit_of_mul_isUnit_right (h2 ▸ h1 : IsUnit (y * u))
  have hϖI : ϖ ∈ I := Ideal.mem_span_singleton_self ϖ
  have hirr : Irreducible ϖ := by
    refine ⟨fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hϖI h), fun a b hab => ?_⟩
    have hprime := hm.isPrime
    have : a * b ∈ I := hab ▸ hϖI
    obtain ha | hb := hprime.mem_or_mem this
    ·
      obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 ha
      right
      have : ϖ * (c * b) = ϖ * 1 := by rw [mul_one, ← mul_assoc, mul_comm ϖ c, hc']; apply hab.symm
      have hcb : c * b = 1 := mul_left_cancel₀ hϖ this
      exact ⟨⟨b, c, by rw [mul_comm] at hcb; apply hcb, hcb⟩, rfl⟩
    ·
      obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 hb
      left
      have : ϖ * (a * c) = ϖ * 1 := by
        rw [mul_one, mul_comm a c, ← mul_assoc, mul_comm ϖ c, hc', mul_comm]; apply hab.symm
      have hac : a * c = 1 := mul_left_cancel₀ hϖ this
      exact ⟨⟨a, c, hac, by rw [mul_comm] at hac; apply hac⟩, rfl⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, ?_⟩
  intro x hx
  have hnot : ∃ n : ℕ, x ∉ Ideal.span {ϖ ^ n} := by
    by_contra hall
    push Not at hall
    apply hx
    apply IsHausdorff.haus hc.toIsHausdorff x
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hI, Ideal.span_singleton_pow]
    apply hall n
  let m := Nat.find hnot
  have hm_spec : x ∉ Ideal.span {ϖ ^ m} := Nat.find_spec hnot
  have hm0 : m ≠ 0 := by
    intro h0
    apply hm_spec
    rw [h0, pow_zero, Ideal.span_singleton_one]; trivial
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hxn : x ∈ Ideal.span {ϖ ^ n} := by
    have := Nat.find_min hnot (show n < m by omega)
    simpa using this
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hxn
  have huI : u ∉ I := by
    intro huI
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 huI
    apply hm_spec
    rw [hn, Ideal.mem_span_singleton']
    exact ⟨c, by rw [pow_succ, ← mul_assoc, ← hu, ← hc']; ring⟩
  obtain ⟨v, hv⟩ := hunit u huI
  exact ⟨n, ⟨v, by rw [hv, mul_comm, hu]⟩⟩


-- created on 2026-10-20
