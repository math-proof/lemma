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
public import Instance.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount.Part2

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- The weight (binary encoding) of a matrix. -/
def Wt (m n : ℕ) (x : Fin m → Fin n → Bool) : ℕ :=
  ∑ r : Fin m, ∑ s : Fin n, (if x r s = true then 1 else 0) * 2 ^ (r.val * n + s.val)

end MetaMathlibExt
