/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.Push

@[expose] public section

namespace MetaMathlibExt

/-! # Fibonacci parity-alternating avoidance -/

def IsGood (n : ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, (π i).val % 2 = i.val % 2) ∧
  (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π j).val < (π k).val ∧ (π k).val < (π i).val)) ∧
  (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π k).val < (π i).val ∧ (π i).val < (π j).val))

end MetaMathlibExt
