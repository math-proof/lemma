/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence.Part2
/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/


namespace MetaMathlibExt

namespace GeneralizedThueMorse

/-- The infinite word `A_∞`: its `m`-th letter is read from the finite block
`A_{m+1}`, proven long enough, via checked indexing with no default letter
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
def infLetter (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (m : Nat) : Fin L :=
  (block L k hL hk kappa (m + 1)).get
    ⟨m, by
      rw [block_length]
      exact lt_pow_succ_self hk m⟩

/-- Classical shift schedule `κ(1, n) = 1`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
def classicalKappa : Fin (2 - 1) → Nat → Fin 2 := fun _ _ => ⟨1, by decide⟩

/-- Classical blocks as a specialization of the general construction
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
def classicalBlock : Nat → List (Fin 2) :=
  block 2 2 (by decide) (by decide) classicalKappa

end GeneralizedThueMorse
end MetaMathlibExt
