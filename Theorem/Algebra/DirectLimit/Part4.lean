import Mathlib
import Def.Algebra.DirectLimit.Part3


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

variable {P₁ P₂ : Type*}

theorem Equiv_apply
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] [IsDirectLimit f g₂] (i : ι) (x : M i) :
    Equiv f g₁ g₂ (g₁ i x) = g₂ i x := by
  apply lift_of f g₁ g₂
  intro i j hij y
  apply compatibility' f g₂ hij y

theorem Equiv_symm_apply
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] [IsDirectLimit f g₂] (i : ι) (x : M i) :
    (Equiv f g₁ g₂).symm (g₂ i x) = g₁ i x := by
  apply lift_of f g₂ g₁
  intro i j hij y
  apply compatibility' f g₁ hij y

end IsDirectLimit
