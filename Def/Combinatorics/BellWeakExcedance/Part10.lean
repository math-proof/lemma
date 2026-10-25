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
import Theorem.Combinatorics.BellWeakExcedance.Part9


section

namespace MetaMathlibExt

noncomputable def ofPartPerm {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (ofPartFun P) (ofPartFun_injective P).bijective_of_finite

end MetaMathlibExt
end
