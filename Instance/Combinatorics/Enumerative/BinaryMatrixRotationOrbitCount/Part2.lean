/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Combinatorics.Colex
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Def.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount.Part2


namespace MetaMathlibExt

open scoped BigOperators

instance finAddCyclic (M : ℕ) [NeZero M] : IsAddCyclic (Fin M) := by
  obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  exact ZMod.instIsAddCyclic (M' + 1)

end MetaMathlibExt
