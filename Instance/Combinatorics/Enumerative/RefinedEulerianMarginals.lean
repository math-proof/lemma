/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RefinedEulerianMarginals.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.RefinedEulerianMarginals

@[expose] public section

namespace MetaMathlibExt

instance desDec (n : ℕ) (σ : Equiv.Perm (Fin n)) : DecidablePred (des n σ) :=
  fun _ => Nat.decLt _ _

end MetaMathlibExt
