/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Composite.lean -/

import Mathlib.Data.Nat.Prime.Defs
/-!
# Composite natural numbers

A shared predicate for natural numbers greater than one that are not prime.
-/


namespace Nat

/-- A natural number is composite if it is greater than one and not prime. -/
def IsComposite (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime

end Nat
