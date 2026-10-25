/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence
/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/


namespace MetaMathlibExt

namespace GeneralizedThueMorse

/-- Finite blocks `Aₙ` of the `(L, k, κ)`-TM sequence
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`):
`A₀` is the one-letter word `a₀`, and `Aₙ₊₁` concatenates `Aₙ` with each
whole-word cyclic shift `f^{κ(j,n)}(Aₙ)` for `j = 1, …, k-1`. -/
def block (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) : Nat → List (Fin L)
  | 0 => [⟨0, by omega⟩]
  | n + 1 =>
    let prev := block L k hL hk kappa n
    prev ++ List.flatten (List.map (fun j => shiftWord (kappa j n) prev) (List.finRange (k - 1)))

end GeneralizedThueMorse
end MetaMathlibExt
