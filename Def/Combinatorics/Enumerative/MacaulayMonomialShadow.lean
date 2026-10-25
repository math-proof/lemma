/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple
import Theorem.Combinatorics.Enumerative.MacaulayMonomialShadow


namespace MetaMathlibExt

open BigOperators

section

/-- The canonical strict binomial cascade, with the empty tuple at rank zero. -/
noncomputable def mms_digits (r n : ℕ) : Fin r → ℕ :=
  if h : 0 < r then Classical.choose (mms_exists_rep r n h)
  else fun i => Fin.elim0 (Nat.eq_zero_of_not_pos h ▸ i)

end
end MetaMathlibExt
