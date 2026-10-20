import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma eq_zero_of_pow_eq_mul_of_pow_mul_eq_zero
  {S : Type u} [CommRing S] [IsReduced S]
  {a x t : S} {n m : ℕ}
  (hn : x ^ n = a * t) (hm : x ^ m * a = 0) :
  -- imply
  x = 0 := by
  -- proof
  apply IsNilpotent.eq_zero
  refine ⟨m + n, ?_⟩
  rw [pow_add, hn, ← mul_assoc, hm, zero_mul]

private lemma mul_eq_zero_of_pow_mul_mul_eq_zero
  {S : Type u} [CommRing S] [IsReduced S]
  {a s : S} {m : ℕ}
  (hm : (a * s) ^ m * a = 0) :
  -- imply
  a * s = 0 := by
  -- proof
  apply IsNilpotent.eq_zero
  refine ⟨m + 1, ?_⟩
  rw [pow_succ, ← mul_assoc, hm, zero_mul]

private lemma mem_annihilator_span_singleton_iff
  {S : Type u} [CommRing S]
  (a r : S) :
  -- imply
  r ∈ (Ideal.span {a} : Submodule S S).annihilator ↔ r * a = 0 := by
  -- proof
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]

private lemma radical_span_inf_radical_annihilator_eq_bot
  {S : Type u} [CommRing S] [IsReduced S]
  (a : S) :
  -- imply
  (Ideal.span {a}).radical ⊓ ((Ideal.span {a} : Submodule S S).annihilator).radical = ⊥ ∧ ∀ s : S, a * s ∈ ((Ideal.span {a} : Submodule S S).annihilator).radical → s ∈ ((Ideal.span {a} : Submodule S S).annihilator).radical := by
  -- proof
  constructor
  ·
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Ideal.mem_bot]
    obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hx1
    obtain ⟨m, hm⟩ := (Ideal.mem_radical_iff).mp hx2
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hn
    rw [mem_annihilator_span_singleton_iff] at hm
    apply eq_zero_of_pow_eq_mul_of_pow_mul_eq_zero (n := n) (m := m) (by rw [← ht, mul_comm]) hm
  ·
    intro s hs
    obtain ⟨m, hm⟩ := (Ideal.mem_radical_iff).mp hs
    rw [mem_annihilator_span_singleton_iff] at hm
    have h0 : a * s = 0 := mul_eq_zero_of_pow_mul_mul_eq_zero hm
    refine Ideal.le_radical ?_
    rw [mem_annihilator_span_singleton_iff, mul_comm]
    apply h0

/--
[Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] [IsReduced S]
  (a : S) :
  -- imply
  (Ideal.span {a}).radical ⊓ ((Ideal.span {a}).annihilator).radical = ⊥ ∧ ∀ s : S, a * s ∈ ((Ideal.span {a}).annihilator).radical → s ∈ ((Ideal.span {a}).annihilator).radical :=
  radical_span_inf_radical_annihilator_eq_bot a


-- created on 2026-10-20
