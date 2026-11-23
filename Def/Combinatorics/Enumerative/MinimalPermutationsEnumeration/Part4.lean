/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

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
public import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part4

@[expose] public section

section

namespace MetaMathlibExt

def topSmall (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Fin (d + 2)) :=
  Finset.Ici ⟨d + 2 - a.val, by have ha := a.isLt; omega⟩

def topLarge (d : ℕ) (a : Fin (d + 1)) : Finset (Fin (d + 2)) :=
  Finset.Ici ⟨d - a.val, by omega⟩

end MetaMathlibExt
end
