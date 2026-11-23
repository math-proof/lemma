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
public import Theorem.Combinatorics.Enumerative.IdentityProductNecklace.Part2

@[expose] public section

section

namespace MetaMathlibExt

/-- The quotient-to-orbit-set map. -/
def neckQuot (G : Type*) [Group G] (n : ℕ) [NeZero n] :
    Quotient (AddAction.orbitRel (ZMod n)
      {x : Fin n → G // (List.ofFn x).prod = 1}) → Set (Fin n → G) :=
  fun q => orbSet G n q.out.val

end MetaMathlibExt
end
