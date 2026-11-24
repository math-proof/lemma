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
public import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
