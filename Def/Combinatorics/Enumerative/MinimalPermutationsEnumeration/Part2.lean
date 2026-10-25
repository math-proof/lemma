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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part2


section

namespace MetaMathlibExt

def block1Pos (d : ℕ) (a : Fin (d + 1)) (i : Fin (a.val + 1)) :
    Fin (d + 2) :=
  ⟨i.val, by have ha := a.isLt; have hi := i.isLt; omega⟩

def block2Pos (d : ℕ) (a : Fin (d + 1)) (i : Fin ((d - a.val) + 1)) :
    Fin (d + 2) :=
  ⟨a.val + 1 + i.val, by have ha := a.isLt; have hi := i.isLt; omega⟩

end MetaMathlibExt
end
