import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma mem_nonZeroDivisors_of_forall_notMem_minimalPrimes {S : Type*} [CommRing S] [IsReduced S] (x : S) (hx : ∀ P ∈ minimalPrimes S, x ∉ P) : x ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  by_contra hy0
  have hnil : y ∉ nilradical S := by rw [nilradical_eq_zero]; apply hy0
  rw [nilradical_eq_sInf, Submodule.mem_sInf] at hnil
  push Not at hnil
  obtain ⟨J, hJ, hyJ⟩ := hnil
  let _ : Ideal.IsPrime J := hJ
  obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal S) ≤ (J : Ideal S) from bot_le)
  have hPmin : P ∈ minimalPrimes S := hP
  let _ : P.IsPrime := hP.1.1
  have hxy : y * x ∈ P := by rw [hy]; apply P.zero_mem
  obtain h | h := Ideal.IsPrime.mem_or_mem inferInstance hxy
  · apply hyJ (hPJ h)
  · apply hx P hPmin h
/--
[RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing B] [Nontrivial B] [Algebra A B] [Module.Finite A B]
    (a b : A) (ha𝔪 : a ∈ IsLocalRing.maximalIdeal A) (hb𝔪 : b ∈ IsLocalRing.maximalIdeal A)
    (ha : IsSMulRegular B (algebraMap A B a))
    (hred : IsReduced (B ⧸ Ideal.span {algebraMap A B a}))
    (hb : ∀ P ∈ minimalPrimes (B ⧸ Ideal.span {algebraMap A B a}),
      Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) (algebraMap A B b) ∉ P) :
    -- imply
    RingTheory.Sequence.IsRegular B [a, b] := by
    -- proof
  refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal B (fun r hr => ?_) ?_
  ·
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain rfl | rfl := hr
    ·
      apply ha𝔪
    ·
      apply hb𝔪
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨?_, ?_, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
  ·
    intro x y h
    apply ha (by simp only [Algebra.smul_def] at h; apply h)
  ·
    have hnzd := mem_nonZeroDivisors_of_forall_notMem_minimalPrimes _ hb
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨z, -, hz⟩ := hx
    have hq : Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) (algebraMap A B b) *
        Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) x = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      refine ⟨z, ?_⟩
      rw [← Algebra.smul_def, ← hz, Algebra.smul_def]
    have hx0 := (mem_nonZeroDivisors_iff_right.mp hnzd) _ (by rwa [mul_comm] at hq)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx0
    obtain ⟨w, hw⟩ := hx0
    exact ⟨w, trivial, by rw [Algebra.smul_def, hw]⟩


-- created on 2026-10-20
