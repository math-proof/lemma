/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Theorem.Combinatorics.BellWeakExcedance.Part8


section

namespace MetaMathlibExt

noncomputable def ofPartFun {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Fin n → Fin n :=
  fun u =>
    if h : u ∈ mins P then
      (maxs P).orderEmbOfFin (card_maxs_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, h⟩)
    else pred P u h

end MetaMathlibExt
end
