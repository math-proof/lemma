import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FibonacciPAPAvoidance
open MetaMathlibExt


/--
[fibonacci_card_parity_alternating_avoiding_312_231](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma fibonacci_card_parity_alternating_avoiding_312_231_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Fintype.card { π : Equiv.Perm (Fin n) //
    (∀ i, (π i).val % 2 = i.val % 2) ∧
    (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π j).val < (π k).val ∧ (π k).val < (π i).val)) ∧
    (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π k).val < (π i).val ∧ (π i).val < (π j).val)) } = Nat.fib n := by
-- proof
  apply MetaMathlibExt.fibonacci_card_parity_alternating_avoiding_312_231 n hn


-- created on 2026-10-20
