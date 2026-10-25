import Mathlib
import Theorem.Algebra.DirectLimit.Part2


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

variable {P₁ P₂ : Type*}

noncomputable def lift
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁] (p : P₁) : P₂ :=
  g₂ (preimage_index f g₁ p) (preimage f g₁ p)

end IsDirectLimit
