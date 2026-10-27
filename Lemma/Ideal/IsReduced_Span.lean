import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsNoetherianRing A]
  (x : A)
  (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ associatedPrimes A (A ⧸ Ideal.span {x}) → Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) = maximalIdeal (Localization.AtPrime P)) :
  -- imply
  IsReduced (A ⧸ Ideal.span {x}) := by
  -- proof
  rw [isReduced_iff]
  intro a ha
  by_contra ha0
  obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A a ha0
  let _ := hP.isPrime
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨n, hn⟩ := ha
  have han : a ^ n ∈ Ideal.span {x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    apply hn
  set S := Localization.AtPrime P with hS
  have hprime : (Ideal.map (algebraMap A S) (Ideal.span {x})).IsPrime := by
    rw [h P hP]
    infer_instance
  have h1 : algebraMap A S a ∈ Ideal.map (algebraMap A S) (Ideal.span {x}) := by
    apply hprime.mem_of_pow_mem n
    rw [← map_pow]
    apply Ideal.mem_map_of_mem _ han
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h1
  obtain ⟨y, hy⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  have h2 : algebraMap A S (b * x) = algebraMap A S (↑s * a) := by
    rw [map_mul, map_mul, ← hy]
    calc
      _ = (algebraMap A S ↑s * IsLocalization.mk' S b s) * algebraMap A S x := by
        rw [IsLocalization.mk'_spec']
      _ = algebraMap A S ↑s * (IsLocalization.mk' S b s * algebraMap A S x) := by
        ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists P.primeCompl S).mp h2
  have hmem : (↑t * ↑s : A) ∈ P := by
    apply hcol
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : ↑t * ↑s * a = (↑t * b) * x := calc
      _ = ↑t * (↑s * a) := by
        ring
      _ = ↑t * (b * x) := ht.symm
      _ = ↑t * b * x := by
        ring
    rw [this]
    apply Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  refine (P.primeCompl.mul_mem t.2 s.2) hmem


-- created on 2026-10-20
