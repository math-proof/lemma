/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Colex
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Instance.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount


namespace MetaMathlibExt

open scoped BigOperators

theorem shift_vadd_apply {m n : ℕ} [NeZero m] [NeZero n]
    (p : Fin m × Fin n) (x : Fin m → Fin n → Bool) (r : Fin m) (s : Fin n) :
    (p +ᵥ x) r s = x (r + p.1) (s + p.2) := rfl

end MetaMathlibExt
