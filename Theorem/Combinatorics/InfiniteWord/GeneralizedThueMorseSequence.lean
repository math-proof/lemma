/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring
import Def.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence
/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/


namespace MetaMathlibExt

namespace GeneralizedThueMorse

/-- Shifting preserves word length
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem shiftWord_length {L : Nat} (t : Fin L) (w : List (Fin L)) :
    (shiftWord t w).length = w.length := by
  simp [shiftWord]

end GeneralizedThueMorse
end MetaMathlibExt
