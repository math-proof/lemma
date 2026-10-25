/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Def.Combinatorics.Enumerative.FibonacciPAPAvoidance


namespace MetaMathlibExt

instance (n : ℕ) : DecidablePred (IsGood n) := fun π => by unfold IsGood; infer_instance

end MetaMathlibExt
