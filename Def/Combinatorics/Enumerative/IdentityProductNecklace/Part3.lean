/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean -/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Instance.Combinatorics.Enumerative.IdentityProductNecklace

@[expose] public section

section

namespace MetaMathlibExt

/-- The rotation-orbit set of a tuple, in the form used by the theorem statement. -/
def orbSet (G : Type*) (n : ℕ) [NeZero n]
    (x : Fin n → G) : Set (Fin n → G) :=
  {y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩}

end MetaMathlibExt
end
