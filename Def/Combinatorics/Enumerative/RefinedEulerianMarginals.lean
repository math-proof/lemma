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

@[expose] public section

namespace MetaMathlibExt

/-- Descent at 1-based adjacent position `i.val + 1` for a permutation of `Fin n`. -/
def des (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) : Prop :=
  (σ ⟨i.val, by have := i.isLt; omega⟩).val >
    (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val

end MetaMathlibExt
