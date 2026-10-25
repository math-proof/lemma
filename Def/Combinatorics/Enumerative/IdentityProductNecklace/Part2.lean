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
import Theorem.Combinatorics.Enumerative.IdentityProductNecklace


section

namespace MetaMathlibExt

/-- The rotation action as a function on identity-product tuples. -/
def rotVAddFun (G : Type*) [Group G] (n : ℕ) [NeZero n]
    (k : ZMod n) (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    {x : Fin n → G // (List.ofFn x).prod = 1} :=
  ⟨rotShift G n k x.val, (rotShift_prod_eq_one G n k x.val).mpr x.prop⟩

end MetaMathlibExt
end
