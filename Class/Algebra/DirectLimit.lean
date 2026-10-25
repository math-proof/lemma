import Mathlib


/-- A cocone `g` exhibits `P` as the direct limit of the transition maps `f`. -/
class IsDirectLimit {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P) [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj : ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj →
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj
  compatibility : ∀ i j (hij : i ≤ j) (x : M i), g j (f i j hij x) = g i x

