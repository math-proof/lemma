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
import Def.Combinatorics.Enumerative.MacaulayMonomialShadow


namespace MetaMathlibExt

open BigOperators

section

lemma mms_digits_strict (r n : ℕ) (hr : 0 < r) : StrictMono (mms_digits r n) := by
  simp only [mms_digits, dite_eq_left hr]
  exact (Classical.choose_spec (mms_exists_rep r n hr)).1

lemma mms_digits_sum (r n : ℕ) (hr : 0 < r) :
    n = ∑ i, Nat.choose (mms_digits r n i) (i.1 + 1) := by
  simp only [mms_digits, dite_eq_left hr]
  exact (Classical.choose_spec (mms_exists_rep r n hr)).2

end
end MetaMathlibExt
