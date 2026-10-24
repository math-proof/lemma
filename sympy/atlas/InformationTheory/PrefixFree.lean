/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/PrefixFree.lean -/

import Mathlib.Data.List.Basic

namespace MathlibExt.InformationTheory

/-- A code is prefix-free when no two distinct source symbols map to words in a
prefix relation. Since the condition quantifies over all ordered pairs of
distinct symbols, both prefix directions are forbidden. -/
def IsPrefixFree {α β : Type*} (code : α → List β) : Prop :=
  ∀ ⦃a₁ a₂ : α⦄, a₁ ≠ a₂ → ¬ code a₁ <+: code a₂
end MathlibExt.InformationTheory
