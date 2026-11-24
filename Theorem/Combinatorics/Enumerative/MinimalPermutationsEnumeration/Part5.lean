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
public import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

theorem topSmall_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (topSmall d a hpos).card = a.val := by
  simp only [topSmall, Fin.card_Ici]
  have ha := a.isLt
  omega

end MetaMathlibExt
end
