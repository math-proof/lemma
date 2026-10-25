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
import Def.Combinatorics.Enumerative.IdentityProductNecklace.Part2


section

namespace MetaMathlibExt

instance rotVAddInst (G : Type*) [Group G] (n : ℕ)
    [NeZero n] :
    VAdd (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1} :=
  ⟨rotVAddFun G n⟩

instance rotAddSemigroupActionInst (G : Type*) [Group G]
    (n : ℕ) [NeZero n] :
    AddSemigroupAction (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1} where
  add_vadd := fun k l x => Subtype.ext (rotShift_add G n k l x.val)

instance rotAddActionInst (G : Type*) [Group G]
    (n : ℕ) [NeZero n] :
    AddAction (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1} where
  zero_vadd := fun x => Subtype.ext (rotShift_zero G n x.val)

instance rotFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) :
    Fintype {x : Fin n → G // (List.ofFn x).prod = 1} := by
  classical
  exact Subtype.fintype _

instance rotFixedByFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) [NeZero n] (k : ZMod n) :
    Fintype ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k) := by
  classical
  exact Subtype.fintype _

instance orbRelSetoid (G : Type*) [Group G]
    (n : ℕ) [NeZero n] :
    Setoid {x : Fin n → G // (List.ofFn x).prod = 1} :=
  AddAction.orbitRel (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1}

noncomputable instance rotQuotFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) [NeZero n] :
    Fintype (Quotient (AddAction.orbitRel (ZMod n)
      {x : Fin n → G // (List.ofFn x).prod = 1})) := by
  classical
  exact Quotient.fintype _

end MetaMathlibExt
end
