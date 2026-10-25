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
import Theorem.Combinatorics.BellWeakExcedance.Part4


section

namespace MetaMathlibExt

noncomputable def mins {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.image fun a =>
    (P.part a).min' (P.part_nonempty.mpr (Finset.mem_univ a))

noncomputable def maxs {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.image fun a =>
    (P.part a).max' (P.part_nonempty.mpr (Finset.mem_univ a))

end MetaMathlibExt
end
