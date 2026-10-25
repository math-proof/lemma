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
import Theorem.Combinatorics.Enumerative.IdentityProductNecklace.Part2


section

namespace MetaMathlibExt

/-- The quotient-to-orbit-set map. -/
def neckQuot (G : Type*) [Group G] (n : ℕ) [NeZero n] :
    Quotient (AddAction.orbitRel (ZMod n)
      {x : Fin n → G // (List.ofFn x).prod = 1}) → Set (Fin n → G) :=
  fun q => orbSet G n q.out.val

end MetaMathlibExt
end
