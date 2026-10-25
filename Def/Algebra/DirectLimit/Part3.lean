import Mathlib
import Theorem.Algebra.DirectLimit.Part3


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

variable {P₁ P₂ : Type*}

noncomputable def Equiv
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] [IsDirectLimit f g₂] : P₁ ≃ P₂ where
  toFun := lift f g₁ g₂
  invFun := lift f g₂ g₁
  left_inv x := by
    obtain ⟨i, mi, hmi⟩ := IsDirectLimit.surj (f := f) (g := g₁) x
    rw [← hmi]
    have hto : lift f g₁ g₂ (g₁ i mi) = g₂ i mi :=
      lift_of f g₁ g₂ (fun i j hij y => compatibility' f g₂ hij y) mi
    rw [hto]
    apply lift_of f g₂ g₁
    intro i j hij y
    apply compatibility' f g₁ hij y
  right_inv x := by
    obtain ⟨i, mi, hmi⟩ := IsDirectLimit.surj (f := f) (g := g₂) x
    rw [← hmi]
    have hto : lift f g₂ g₁ (g₂ i mi) = g₁ i mi :=
      lift_of f g₂ g₁ (fun i j hij y => compatibility' f g₁ hij y) mi
    rw [hto]
    apply lift_of f g₁ g₂
    intro i j hij y
    apply compatibility' f g₂ hij y

end IsDirectLimit
