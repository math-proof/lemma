/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RefinedEulerianMarginals.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- Descent at 1-based adjacent position `i.val + 1` for a permutation of `Fin n`. -/
private def des (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) : Prop :=
  (σ ⟨i.val, by have := i.isLt; omega⟩).val >
    (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val

private instance desDec (n : ℕ) (σ : Equiv.Perm (Fin n)) : DecidablePred (des n σ) :=
  fun _ => Nat.decLt _ _
end MetaMathlibExt
