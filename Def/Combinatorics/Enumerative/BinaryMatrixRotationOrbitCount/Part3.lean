/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Colex
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Instance.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount.Part2


namespace MetaMathlibExt

open scoped BigOperators

/-- The weight (binary encoding) of a matrix. -/
def Wt (m n : ℕ) (x : Fin m → Fin n → Bool) : ℕ :=
  ∑ r : Fin m, ∑ s : Fin n, (if x r s = true then 1 else 0) * 2 ^ (r.val * n + s.val)

end MetaMathlibExt
