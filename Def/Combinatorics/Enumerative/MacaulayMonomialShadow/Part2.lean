/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Fin.Tuple
public import Theorem.Combinatorics.Enumerative.MacaulayMonomialShadow.Part2

@[expose] public section

namespace MetaMathlibExt

open BigOperators

section

/-- The Macaulay lower function read from the canonical cascade. -/
noncomputable def mms_macaulay (r n : ℕ) : ℕ :=
  ∑ i, if mms_digits r n i = 0 then 0
    else Nat.choose (mms_digits r n i - 1) i.1

end
end MetaMathlibExt
