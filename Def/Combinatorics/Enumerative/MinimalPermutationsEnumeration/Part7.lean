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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part7


section

namespace MetaMathlibExt

def mpeFirstIndex (d : ℕ) (a : Fin (d + 1)) (p : Fin (d + 2))
    (h : p.val ≤ a.val) : Fin (a.val + 1) :=
  ⟨p.val, by omega⟩

end MetaMathlibExt
end
