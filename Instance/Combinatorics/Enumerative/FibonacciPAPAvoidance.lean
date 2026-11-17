/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.Push
public import Def.Combinatorics.Enumerative.FibonacciPAPAvoidance

@[expose] public section

namespace MetaMathlibExt

instance (n : ℕ) : DecidablePred (IsGood n) := fun π => by unfold IsGood; infer_instance

end MetaMathlibExt
