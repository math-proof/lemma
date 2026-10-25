import Mathlib
import Class.Algebra.DirectLimit


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

theorem compatibility' {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] {i j : ι} (hij : i ≤ j) (x : M i) :
    g j (f i j hij x) = g i x :=
  IsDirectLimit.compatibility i j hij x

theorem is_injective {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] {i j : ι} {mi : M i} {mj : M j}
    (h : g i mi = g j mj) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
  IsDirectLimit.inj i j mi mj h

theorem is_surjective {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (m : P) :
    ∃ i, ∃ mi : M i, g i mi = m :=
  IsDirectLimit.surj (f := f) (g := g) m

end IsDirectLimit
