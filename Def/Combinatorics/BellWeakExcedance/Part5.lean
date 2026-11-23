/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

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
public import Theorem.Combinatorics.BellWeakExcedance.Part4

@[expose] public section

section

namespace MetaMathlibExt

noncomputable def mins {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.image fun a =>
    (P.part a).min' (P.part_nonempty.mpr (Finset.mem_univ a))

noncomputable def maxs {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.image fun a =>
    (P.part a).max' (P.part_nonempty.mpr (Finset.mem_univ a))

end MetaMathlibExt
end
