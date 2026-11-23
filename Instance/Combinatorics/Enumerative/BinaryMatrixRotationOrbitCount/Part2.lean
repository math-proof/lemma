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
public import Def.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount.Part2
@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

instance finAddCyclic (M : ℕ) [NeZero M] : IsAddCyclic (Fin M) := by
  obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  exact ZMod.instIsAddCyclic (M' + 1)

end MetaMathlibExt
