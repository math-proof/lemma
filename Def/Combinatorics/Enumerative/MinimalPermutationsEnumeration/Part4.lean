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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part4


section

namespace MetaMathlibExt

def topSmall (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Fin (d + 2)) :=
  Finset.Ici ⟨d + 2 - a.val, by have ha := a.isLt; omega⟩

def topLarge (d : ℕ) (a : Fin (d + 1)) : Finset (Fin (d + 2)) :=
  Finset.Ici ⟨d - a.val, by omega⟩

end MetaMathlibExt
end
