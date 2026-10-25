import Mathlib
import Def.Algebra.DirectLimit


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

theorem image_preimage {P : Type*}
    (f : (i j : ι) → i ≤ j → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] [IsDirectLimit f g] (p : P) :
    g (preimage_index f g p) (preimage f g p) = p :=
  (is_surjective f g p).choose_spec.choose_spec

end IsDirectLimit
