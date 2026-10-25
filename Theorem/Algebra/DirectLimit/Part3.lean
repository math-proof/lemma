import Mathlib
import Def.Algebra.DirectLimit.Part2


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

variable {P₁ P₂ : Type*}

theorem lift_of
    (f : (i j : ι) → i ≤ j → M i → M j) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
    [DirectedSystem M f] [IsDirectLimit f g₁]
    (Hg : ∀ i j (hij : i ≤ j) (x : M i), g₂ j (f i j hij x) = g₂ i x) {i : ι} (x : M i) :
    lift f g₁ g₂ (g₁ i x) = g₂ i x := by
  dsimp [lift]
  obtain ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]

end IsDirectLimit
