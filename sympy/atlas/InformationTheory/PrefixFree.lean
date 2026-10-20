/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean -/

import Mathlib.Data.List.Basic

namespace MathlibExt.InformationTheory

/-- A code is prefix-free when no two distinct source symbols map to words in a
prefix relation. Since the condition quantifies over all ordered pairs of
distinct symbols, both prefix directions are forbidden. -/
def IsPrefixFree {α β : Type*} (code : α → List β) : Prop :=
  ∀ ⦃a₁ a₂ : α⦄, a₁ ≠ a₂ → ¬ code a₁ <+: code a₂

/-- In a prefix-free code, a prefix relation between codewords forces equality
of the source symbols. -/
theorem IsPrefixFree.eq_of_isPrefix {α β : Type*} {code : α → List β}
    (h : IsPrefixFree code) {a₁ a₂ : α} (hpre : code a₁ <+: code a₂) :
    a₁ = a₂ := by
  by_contra hne
  exact h hne hpre

/-- A prefix-free code is injective: equal codewords are mutually prefix, hence
come from equal symbols. -/
theorem IsPrefixFree.injective {α β : Type*} {code : α → List β}
    (h : IsPrefixFree code) : Function.Injective code := by
  intro a₁ a₂ heq
  by_contra hne
  exact h hne ⟨[], by simp [heq]⟩

/-- If a prefix-free code assigns the empty word to one symbol, that symbol is
the only one: `[]` is a prefix of every word. -/
theorem IsPrefixFree.eq_of_mem_nil {α β : Type*} {code : α → List β}
    (h : IsPrefixFree code) {a₀ : α} (ha₀ : code a₀ = []) (a : α) :
    a = a₀ := by
  by_contra hne
  apply h (fun heq => hne heq.symm) _
  rw [ha₀]
  exact ⟨_, rfl⟩

end MathlibExt.InformationTheory
