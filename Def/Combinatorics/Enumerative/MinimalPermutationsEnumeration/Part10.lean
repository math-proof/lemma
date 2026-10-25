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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part10


section

namespace MetaMathlibExt

noncomputable def mpeConstruct (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Equiv.Perm (Fin (d + 2)) :=
  Equiv.ofBijective (mpeConstructFun d a L hL)
    (mpeConstructFun_injective d a L hL).bijective_of_finite

end MetaMathlibExt
end
