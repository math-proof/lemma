import Mathlib


/-! An implementation of finite choice, see https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Theorem.20for.20.22finite.20choice.22.3F/with/529925010 -/

theorem finite_choice {X:Type*} {f:X → ℕ} {N:ℕ} (h: ∀ n < N, ∃ x, f x = n) :
  ∃ g: Fin N → X, ∀ n, f (g n) = n := by
  induction' N with N ih
  . simp only [IsEmpty.forall_iff, exists_const]
  specialize ih ?_
  . intro n hn; exact h n (Nat.lt_add_right 1 hn)
  obtain ⟨ g, hg ⟩ := ih
  obtain ⟨ x, hx ⟩ := h N (Nat.lt_add_one N)
  set g' : Fin (N+1) → X := fun n ↦ if h:n.val < N then g ⟨ n.val, h ⟩ else x
  use g'
  intro n; by_cases h:n.val < N
  . simp only [g', dif_pos h, hg]
  convert hx
  . simp only [g', dif_neg h]
  exact Nat.eq_of_lt_succ_of_not_lt n.isLt h

lemma sec_ex {α β:Type*} [Fintype β] [DecidableEq β] (f : α → β) (h : ∀ b: β, ∃ a : α, f a = b) : ∃ s :β → α, f ∘ s = id := by
  set N := Fintype.card β
  have : Fintype.card β = N := rfl
  have := (Fintype.truncEquivFinOfCardEq this)
  obtain ⟨ e, _ ⟩ := (Fintype.truncEquivFinOfCardEq (show Fintype.card β = N by rfl)).exists_rep
  set F: α → ℕ := fun a ↦ (e (f a)).val
  replace h : ∀ n < N, ∃ x, F x = n := by
    intro n hn
    obtain ⟨ a, ha ⟩ := h (e.symm ⟨ n, hn ⟩)
    use a; simp only [ha, Equiv.apply_symm_apply, F]
  obtain ⟨ g, hg ⟩ := finite_choice h; use g ∘ e
  ext b; specialize hg (e b)
  simpa only [Function.comp_apply, id_eq, Fin.val_inj, EmbeddingLike.apply_eq_iff_eq, F] using hg

