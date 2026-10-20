import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma aux
  {α : Type u} (S : α → α → Prop) {b c : α}
  (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧ ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
  -- imply
  ∀ (n : ℕ) (a : α) (f : Fin (n + 1) → α), f 0 = a → f (Fin.last n) = b → (∀ i : Fin n, S (f i.castSucc) (f i.succ)) → ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧ ∀ i : Fin n, S (f i.castSucc) (f i.succ) := by
  -- proof
  intro n
  induction n with
  | zero =>
    intro a f hf0 hfn _
    have hab : a = b := by
      rw [← hf0, ← hfn]
      rfl
    subst hab
    apply h₂
  | succ n ih =>
    intro a f hf0 hfn hfS
    have hlast : f (Fin.last n).succ = b := by
      rw [Fin.succ_last]
      apply hfn
    have hSsucc : ∀ i : Fin n, S (f i.succ.castSucc) (f i.succ.succ) := fun i => by
      have hthis := hfS i.succ
      rwa [← Fin.succ_castSucc] at hthis
    obtain ⟨m, g, hg0, hgm, hgS⟩ := ih (f 1) (fun i => f i.succ) rfl hlast hSsucc
    refine ⟨m + 1, Matrix.vecCons a g, rfl, ?_, ?_⟩
    ·
      rw [← Fin.succ_last, Matrix.cons_val_succ]
      apply hgm
    ·
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      ·
        have h01 := hfS 0
        rw [Fin.castSucc_zero, hf0] at h01
        change S (Matrix.vecCons a g (0 : Fin (m + 1)).castSucc) (Matrix.vecCons a g (0 : Fin (m + 1)).succ)
        rw [Fin.castSucc_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, hg0]
        apply h01
      ·
        change S (Matrix.vecCons a g j.succ.castSucc) (Matrix.vecCons a g j.succ.succ)
        rw [← Fin.succ_castSucc, Matrix.cons_val_succ, Matrix.cons_val_succ]
        apply hgS j

/--
[Fin_exists_chain_append](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Fin_exists_chain_append.lean)
-/
@[path]
private lemma main
  {α : Type u} (S : α → α → Prop) {a b c : α}
  (h₁ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = b ∧ ∀ i : Fin n, S (f i.castSucc) (f i.succ))
  (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧ ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
  -- imply
  ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧ ∀ i : Fin n, S (f i.castSucc) (f i.succ) := by
  -- proof
  obtain ⟨n, f, hf0, hfn, hfS⟩ := h₁
  apply aux S h₂ n a f hf0 hfn hfS


-- created on 2026-10-20
