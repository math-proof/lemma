/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Instance.Combinatorics.Enumerative.IdentityProductNecklace


section

namespace MetaMathlibExt

/-- The rotation-orbit set of a tuple, in the form used by the theorem statement. -/
def orbSet (G : Type*) (n : ℕ) [NeZero n]
    (x : Fin n → G) : Set (Fin n → G) :=
  {y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩}

end MetaMathlibExt
end
