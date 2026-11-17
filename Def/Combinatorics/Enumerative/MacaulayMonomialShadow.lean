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
public import Theorem.Combinatorics.Enumerative.MacaulayMonomialShadow

@[expose] public section

namespace MetaMathlibExt

open BigOperators

section

/-- The canonical strict binomial cascade, with the empty tuple at rank zero. -/
noncomputable def mms_digits (r n : ℕ) : Fin r → ℕ :=
  if h : 0 < r then Classical.choose (mms_exists_rep r n h)
  else fun i => Fin.elim0 (Nat.eq_zero_of_not_pos h ▸ i)

end
end MetaMathlibExt
