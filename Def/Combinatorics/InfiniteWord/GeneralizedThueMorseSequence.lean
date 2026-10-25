/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring
/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/


namespace MetaMathlibExt

namespace GeneralizedThueMorse

/-- Cyclic letter shift for the `(L, k, κ)`-TM sequence
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statements
`jis_099e0392547ec836b0b913d1`/`jis_6d78ade850f143086b5f8774`):
sends `aᵢ` to `a_{i+t}` with the index taken modulo `L`. -/
def shiftLetter {L : Nat} (a t : Fin L) : Fin L :=
  ⟨(a.val + t.val) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.2)⟩

/-- Letterwise action of a cyclic shift on words
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statements
`jis_099e0392547ec836b0b913d1`/`jis_6d78ade850f143086b5f8774`). -/
def shiftWord {L : Nat} (t : Fin L) (w : List (Fin L)) : List (Fin L) :=
  List.map (fun a => shiftLetter a t) w

end GeneralizedThueMorse
end MetaMathlibExt
