module
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Fin.Basic
public import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

theorem mpeSecondIndex_val (d : ℕ) (a : Fin (d + 1)) (p : Fin (d + 2))
    (h : ¬p.val ≤ a.val) :
    (mpeSecondIndex d a p h).val = p.val - (a.val + 1) := rfl

end MetaMathlibExt
end
