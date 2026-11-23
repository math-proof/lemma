/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Combinatorics.Colex
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Abel
public import Instance.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount

public section

namespace MetaMathlibExt

open scoped BigOperators

theorem shift_vadd_apply {m n : ℕ} [NeZero m] [NeZero n]
    (p : Fin m × Fin n) (x : Fin m → Fin n → Bool) (r : Fin m) (s : Fin n) :
    (p +ᵥ x) r s = x (r + p.1) (s + p.2) := rfl

end MetaMathlibExt
