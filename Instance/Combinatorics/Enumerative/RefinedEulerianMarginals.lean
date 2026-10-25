/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RefinedEulerianMarginals.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.RefinedEulerianMarginals


namespace MetaMathlibExt

instance desDec (n : ℕ) (σ : Equiv.Perm (Fin n)) : DecidablePred (des n σ) :=
  fun _ => Nat.decLt _ _

end MetaMathlibExt
