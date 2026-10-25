/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Colex
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Def.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount


namespace MetaMathlibExt

open scoped BigOperators

/-- The cyclic shift action of `Fin m × Fin n` on binary matrices. -/
instance shiftAction (m n : ℕ) [NeZero m] [NeZero n] :
    AddAction (Fin m × Fin n) (Fin m → Fin n → Bool) where
  vadd p x := fun r s => x (r + p.1) (s + p.2)
  zero_vadd x := by
    funext r s
    change x (r + (0 : Fin m)) (s + (0 : Fin n)) = x r s
    rw [add_zero, add_zero]
  add_vadd p q x := by
    funext r s
    change x (r + (p.1 + q.1)) (s + (p.2 + q.2)) = x (r + p.1 + q.1) (s + p.2 + q.2)
    rw [add_assoc, add_assoc]

end MetaMathlibExt
