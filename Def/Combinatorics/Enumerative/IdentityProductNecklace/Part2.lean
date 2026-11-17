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
public import Theorem.Combinatorics.Enumerative.IdentityProductNecklace

@[expose] public section

section

namespace MetaMathlibExt

/-- The rotation action as a function on identity-product tuples. -/
def rotVAddFun (G : Type*) [Group G] (n : ℕ) [NeZero n]
    (k : ZMod n) (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    {x : Fin n → G // (List.ofFn x).prod = 1} :=
  ⟨rotShift G n k x.val, (rotShift_prod_eq_one G n k x.val).mpr x.prop⟩

end MetaMathlibExt
end
