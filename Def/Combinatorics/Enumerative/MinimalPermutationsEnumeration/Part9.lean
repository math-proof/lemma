/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part9


section

namespace MetaMathlibExt

noncomputable def mpeConstructFun (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Fin (d + 2) → Fin (d + 2) := fun p =>
  if h : p.val ≤ a.val then
    L.orderEmbOfFin hL (Fin.rev (mpeFirstIndex d a p h))
  else
    Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)
      (Fin.rev (mpeSecondIndex d a p h))

end MetaMathlibExt
end
