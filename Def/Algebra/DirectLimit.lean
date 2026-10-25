import Mathlib
import Theorem.Algebra.DirectLimit


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

noncomputable def preimage_index {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (p : P) : ι :=
  (is_surjective f g p).choose

noncomputable def preimage {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (p : P) : M (preimage_index f g p) :=
  (is_surjective f g p).choose_spec.choose

end IsDirectLimit
