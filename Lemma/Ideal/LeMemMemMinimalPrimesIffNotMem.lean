import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem.lean)
-/
@[path]
private lemma main
  [CommRing B] [IsNoetherianRing B]
  {Q Q' : Ideal B} [Q.IsPrime] [Q'.IsPrime]
  {π : B}
  -- given
  (hle : Q' ≤ Q)
  (hπ : π ∈ Q')
  (h : ∀ p : Ideal B, p.IsPrime → p ≤ Q → (p ∈ minimalPrimes B ↔ π ∉ p)) :
  -- imply
  Q' = Q := by
  -- proof
  classical
  by_contra hne
  have hlt : Q' < Q := lt_of_le_of_ne hle hne
  have h0 : ∀ p : Ideal B, p.IsPrime → p ≤ Q → π ∈ p → p.height ≠ 0 := fun p hp hpQ hπp hh => (Iff.mp (h p hp hpQ) (Iff.mp Ideal.height_eq_zero_iff hh)) hπp
  have hlow : ∀ p q : Ideal B, p.IsPrime → q.IsPrime → q < p → p.height ≤ 1 → q.height = 0 := by
    intro p q hp hq hqp hp1
    have := Iff.mp (Ideal.height_le_iff (p := p) (n := 1)) (by exact_mod_cast hp1) q hq hqp
    apply Iff.mp Order.lt_one_iff (by exact_mod_cast this)
  let S : Set (Ideal B) := minimalPrimes B ∪ (Ideal.span {π}).minimalPrimes
  have hSfin : S.Finite := Set.Finite.union (minimalPrimes.finite_of_isNoetherianRing B) (Ideal.finite_minimalPrimes_of_isNoetherianRing B _)
  have hSprime : ∀ p ∈ S, p.IsPrime := by
    intro p hpS
    obtain hp | hp := hpS
    · apply hp.1.1
    · apply hp.1.1
  have hSht : ∀ p ∈ S, p.height ≤ 1 := by
    intro p hpS
    obtain hp | hp := hpS
    ·
      let _ : p.IsPrime := hp.1.1
      rw [Iff.mpr Ideal.height_eq_zero_iff hp]
      apply bot_le
    · apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
  have hQS : ∀ p ∈ S, ¬ Q ≤ p := by
    intro p hpS hQp
    let _ := hSprime p hpS
    apply h0 Q' ‹_› hle hπ (hlow p Q' ‹_› ‹_› (lt_of_lt_of_le hlt hQp) (hSht p hpS))
  obtain ⟨x, hxQ, hxS⟩ : ∃ x ∈ Q, ∀ p ∈ S, x ∉ p := by
    have key : ¬ ((Q : Set B) ⊆ ⋃ p ∈ (↑hSfin.toFinset : Set (Ideal B)), ((id p : Ideal B) : Set B)) := by
      rw [Ideal.subset_union_prime (R := B) (s := hSfin.toFinset) (f := id) ⊥ ⊥ (fun p hp _ _ => hSprime p (Iff.mp hSfin.mem_toFinset hp))]
      rintro ⟨p, hp, hQp⟩
      apply hQS p (Iff.mp hSfin.mem_toFinset hp) hQp
    rw [Set.not_subset] at key
    obtain ⟨x, hxQ, hx⟩ := key
    refine ⟨x, hxQ, fun p hp hxp => hx ?_⟩
    simp only [Set.Finite.coe_toFinset, id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    exact ⟨p, hp, hxp⟩
  obtain ⟨P₁, hP₁, hP₁Q⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := Q) (Iff.mpr (Ideal.span_singleton_le_iff_mem _) hxQ)
  let hP₁pr : P₁.IsPrime := hP₁.1.1
  have hxP₁ : x ∈ P₁ := hP₁.1.2 (Ideal.mem_span_singleton_self x)
  have hP₁ht : P₁.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP₁
  have hπP₁ : π ∈ P₁ := by
    by_contra hπP₁
    apply hxS P₁ (Or.inl (Iff.mpr (h P₁ hP₁pr hP₁Q) hπP₁)) hxP₁
  obtain ⟨P₂, hP₂, hP₂P₁⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {π}) (J := P₁) (Iff.mpr (Ideal.span_singleton_le_iff_mem _) hπP₁)
  let hP₂pr : P₂.IsPrime := hP₂.1.1
  apply h0 P₂ hP₂pr (hP₂P₁.trans hP₁Q) (hP₂.1.2 (Ideal.mem_span_singleton_self π)) (hlow P₁ P₂ hP₁pr hP₂pr (lt_of_le_of_ne hP₂P₁ fun e => hxS P₂ (Or.inr hP₂) (e ▸ hxP₁)) hP₁ht)


-- created on 2026-10-20
