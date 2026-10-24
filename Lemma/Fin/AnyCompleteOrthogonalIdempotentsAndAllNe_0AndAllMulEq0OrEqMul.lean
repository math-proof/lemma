import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private def Good {B : Type*} [CommRing B] (f : B) (s : Finset B) : Prop := (∀ e ∈ s, IsIdempotentElem e) ∧ (∀ e ∈ s, e ≠ 0) ∧ (∀ e ∈ s, e * f = e) ∧ (∀ e ∈ s, ∀ x : B, IsIdempotentElem x → x * e = 0 ∨ x * e = e) ∧ (∀ e ∈ s, ∀ e' ∈ s, e ≠ e' → e * e' = 0) ∧ (∑ e ∈ s, e = f)
private lemma Good.idem {B : Type*} [CommRing B] {f : B} {s : Finset B} (h : Good f s) : ∀ e ∈ s, IsIdempotentElem e := h.1
private lemma Good.ne {B : Type*} [CommRing B] {f : B} {s : Finset B} (h : Good f s) : ∀ e ∈ s, e ≠ 0 := h.2.1
private lemma Good.le {B : Type*} [CommRing B] {f : B} {s : Finset B} (h : Good f s) : ∀ e ∈ s, e * f = e := h.2.2.1
private lemma Good.prim {B : Type*} [CommRing B] {f : B} {s : Finset B} (h : Good f s) : ∀ e ∈ s, ∀ x : B, IsIdempotentElem x → x * e = 0 ∨ x * e = e := h.2.2.2.1
private lemma Good.ortho {B : Type*} [CommRing B] {f : B} {s : Finset B} (h : Good f s) : ∀ e ∈ s, ∀ e' ∈ s, e ≠ e' → e * e' = 0 := h.2.2.2.2.1
private lemma Good.sum {B : Type*} [CommRing B] {f : B} {s : Finset B} (h : Good f s) : ∑ e ∈ s, e = f := h.2.2.2.2.2
private lemma good_zero {B : Type*} [CommRing B] : Good (0 : B) ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
private lemma good_prim {B : Type*} [CommRing B] {f : B} (hf : IsIdempotentElem f) (hf0 : f ≠ 0) (hprim : ∀ x : B, IsIdempotentElem x → x * f = 0 ∨ x * f = f) : Good f {f} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    simp
    apply hf
  ·
    simp
    apply hf0
  ·
    simp
    apply hf.eq
  ·
    simp
    apply hprim
  · simp
  · simp
private lemma good_union {B : Type*} [CommRing B] [DecidableEq B] {f₁ f₂ : B} {s₁ s₂ : Finset B} (h₁ : Good f₁ s₁) (h₂ : Good f₂ s₂) (h12 : f₁ * f₂ = 0) : Good (f₁ + f₂) (s₁ ∪ s₂) := by
  have hcross : ∀ e ∈ s₁, ∀ e' ∈ s₂, e * e' = 0 := fun e he e' he' => by
    have : e * e' = (e * f₁) * (e' * f₂) := by
      rw [h₁.le e he, h₂.le e' he']
    rw [this]
    calc
      _ = e * e' * (f₁ * f₂) := by
        ring
      _ = 0 := by
        rw [h12, mul_zero]
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro e he he'
    have h0 := hcross e he e he'
    rw [(h₁.idem e he).eq] at h0
    apply h₁.ne e he h0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro e he
    obtain h | h := Finset.mem_union.mp he
    · apply h₁.idem e h
    · apply h₂.idem e h
  ·
    intro e he
    obtain h | h := Finset.mem_union.mp he
    · apply h₁.ne e h
    · apply h₂.ne e h
  ·
    intro e he
    obtain h | h := Finset.mem_union.mp he
    ·
      have hsum0 : ∑ e' ∈ s₂, e * e' = 0 := by
        apply Finset.sum_eq_zero
        intro e' he'
        apply hcross e h e' he'
      rw [mul_add, h₁.le e h, ← h₂.sum, Finset.mul_sum, hsum0, add_zero]
    ·
      have hsum0 : ∑ e' ∈ s₁, e * e' = 0 := by
        apply Finset.sum_eq_zero
        intro e' he'
        rw [mul_comm]
        apply hcross e' he' e h
      rw [mul_add, h₂.le e h, ← h₁.sum, Finset.mul_sum, hsum0, zero_add]
  ·
    intro e he
    obtain h | h := Finset.mem_union.mp he
    · apply h₁.prim e h
    · apply h₂.prim e h
  ·
    intro e he e' he' hne
    obtain h | h := Finset.mem_union.mp he
    ·
      obtain h' | h' := Finset.mem_union.mp he'
      · apply h₁.ortho e h e' h' hne
      · apply hcross e h e' h'
    ·
      obtain h' | h' := Finset.mem_union.mp he'
      ·
        rw [mul_comm]
        apply hcross e' h' e h
      · apply h₂.ortho e h e' h' hne
  · rw [Finset.sum_union hdisj, h₁.sum, h₂.sum]
private lemma exists_good {B : Type*} [CommRing B] [IsNoetherianRing B] (f : B) (hf : IsIdempotentElem f) : ∃ s : Finset B, Good f s := by
  classical
  suffices H : ∀ I : Ideal B, ∀ f : B, IsIdempotentElem f → Ideal.span {1 - f} = I → ∃ s : Finset B, Good f s from
    H _ f hf rfl
  intro I
  refine (wellFounded_gt (α := Ideal B)).induction (C := fun J => ∀ f : B, IsIdempotentElem f → Ideal.span {1 - f} = J → ∃ s : Finset B, Good f s) I ?_
  intro I ih f hf hI
  if hf0 : f = 0 then
    exact ⟨∅, hf0 ▸ good_zero⟩
  else if hprim : ∀ x : B, IsIdempotentElem x → x * f = 0 ∨ x * f = f then
    exact ⟨{f}, good_prim hf hf0 hprim⟩
  else
    push Not at hprim
    obtain ⟨x, hx, hx0, hxf⟩ := hprim
    set f₁ := x * f with hf₁
    set f₂ := f - x * f with hf₂
    have hf₁i : IsIdempotentElem f₁ := hx.mul hf
    have hf₁f : f₁ * f = f₁ := by
      rw [hf₁, mul_assoc, hf.eq]
    have hf₂i : IsIdempotentElem f₂ := by
      change f₂ * f₂ = f₂
      rw [hf₂, sub_mul, mul_sub, mul_sub, hf.eq, hf₁f, mul_comm f f₁, hf₁f, hf₁i.eq, sub_self, sub_zero]
    have hf₂f : f₂ * f = f₂ := by
      rw [hf₂, sub_mul, hf.eq, hf₁f]
    have h12 : f₁ * f₂ = 0 := by
      rw [hf₂, mul_sub, hf₁f, hf₁i.eq, sub_self]
    have hsum : f₁ + f₂ = f := by
      rw [hf₂]
      ring
    have hgt : ∀ g : B, IsIdempotentElem g → g * f = g → g ≠ f → Ideal.span {1 - g} > I := by
      intro g hg hgf hgne
      rw [← hI]
      refine lt_of_le_of_ne ?_ ?_
      ·
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
        refine ⟨1 - f, ?_⟩
        rw [mul_sub, mul_one, sub_mul, one_mul, hgf]
        ring
      ·
        intro heq
        have : (1 - g) ∈ Ideal.span {1 - f} := by
          rw [heq]
          apply Ideal.mem_span_singleton_self _
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp this
        have := congrArg (· * f) hy
        simp [mul_assoc, sub_mul, one_mul, hf.eq, sub_self, mul_zero] at this
        rw [hgf] at this
        apply hgne (sub_eq_zero.mp this.symm).symm
    have hf₂ne : f₂ ≠ f := by
      intro h
      apply hx0
      rw [hf₂] at h
      rw [hf₁]
      linear_combination -h
    obtain ⟨s₁, hs₁⟩ := ih _ (hgt f₁ hf₁i hf₁f hxf) f₁ hf₁i rfl
    obtain ⟨s₂, hs₂⟩ := ih _ (hgt f₂ hf₂i hf₂f hf₂ne) f₂ hf₂i rfl
    exact ⟨s₁ ∪ s₂, hsum ▸ good_union hs₁ hs₂ h12⟩
/--
[IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq.lean)
-/
@[path]
private lemma main
  (B : Type*) [CommRing B] [IsNoetherianRing B] :
  -- imply
  ∃ (n : ℕ) (e : Fin n → B), CompleteOrthogonalIdempotents e ∧
    ∀ i : Fin n, e i ≠ 0 ∧ ∀ x : B, IsIdempotentElem x → x * e i = 0 ∨ x * e i = e i := by
  -- proof
  classical
  obtain ⟨s, hs⟩ := exists_good (1 : B) IsIdempotentElem.one
  refine ⟨s.card, fun i => ((s.equivFin.symm i : s) : B), ⟨⟨fun i => hs.idem _ (s.equivFin.symm i).2, ?_⟩, ?_⟩, fun i => ⟨hs.ne _ (s.equivFin.symm i).2, hs.prim _ (s.equivFin.symm i).2⟩⟩
  ·
    intro i j hij
    apply hs.ortho _ (s.equivFin.symm i).2 _ (s.equivFin.symm j).2
    intro h
    apply hij (s.equivFin.symm.injective (Subtype.ext h))
  ·
    rw [← hs.sum, ← Finset.sum_coe_sort s (fun e => e)]
    apply Fintype.sum_equiv s.equivFin.symm _ _ (fun i => rfl)


-- created on 2026-10-20
