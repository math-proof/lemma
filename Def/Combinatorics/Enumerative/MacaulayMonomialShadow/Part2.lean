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
import Theorem.Combinatorics.Enumerative.MacaulayMonomialShadow.Part2


namespace MetaMathlibExt

open BigOperators

section

/-- The Macaulay lower function read from the canonical cascade. -/
noncomputable def mms_macaulay (r n : ℕ) : ℕ :=
  ∑ i, if mms_digits r n i = 0 then 0
    else Nat.choose (mms_digits r n i - 1) i.1

end
end MetaMathlibExt
