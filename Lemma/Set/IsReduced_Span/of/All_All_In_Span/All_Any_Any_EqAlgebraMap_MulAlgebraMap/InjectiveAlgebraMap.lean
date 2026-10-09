import Mathlib
import sympy.Basic


/--
[IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem.lean)
-/
@[path]
private lemma main
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {p : A} [IsReduced (B ⧸ Ideal.span {algebraMap A B p})]
  {S : Set A}
-- given
  (hinj : Function.Injective (algebraMap A B))
  (hS : ∀ b : B, ∃ s ∈ S, ∃ a : A, algebraMap A B a = algebraMap A B s * b)
  (htf : ∀ s ∈ S, ∀ a : A, s * a ∈ Ideal.span {p} → a ∈ Ideal.span {p}) :
-- imply
  IsReduced (A ⧸ Ideal.span {p}) := by
-- proof
  rw [← Ideal.isRadical_iff_quotient_reduced]
  intro a ⟨n, hn⟩

  have hB : (Ideal.Quotient.mk (Ideal.span {algebraMap A B p})) (algebraMap A B a) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← Set.image_singleton,
      ← Ideal.map_span]
    exact Ideal.mem_map_of_mem _ hn
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hB
  obtain ⟨b, hb⟩ := hB
  obtain ⟨s, hs, a', ha'⟩ := hS b

  have : algebraMap A B (s * a) = algebraMap A B (a' * p) := by
    rw [map_mul, map_mul, ← hb, ha']
    ring
  have hsa : s * a ∈ Ideal.span {p} := by
    rw [hinj this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  exact htf s hs a hsa


-- created on 2026-10-05
