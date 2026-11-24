module
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Theorem.Combinatorics.BellWeakExcedance.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

noncomputable def ofPartFun {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Fin n → Fin n :=
  fun u =>
    if h : u ∈ mins P then
      (maxs P).orderEmbOfFin (card_maxs_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, h⟩)
    else pred P u h

end MetaMathlibExt
end
