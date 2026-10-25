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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration


section

namespace MetaMathlibExt

def prevPos (d : ℕ) (a : Fin (d + 1)) (h : 0 < a.val) : Fin (d + 2) :=
  ⟨a.val - 1, by have ha := a.isLt; omega⟩

def nextPos (d : ℕ) (a : Fin (d + 1)) (h : a.val < d) : Fin (d + 2) :=
  ⟨a.val + 2, by have ha := a.isLt; omega⟩

end MetaMathlibExt
end
