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

@[expose] public section

section

namespace MetaMathlibExt

/-- Rotation of a tuple by `k` positions (forward shift of indices). -/
def rotShift (G : Type*) (n : ℕ) [NeZero n]
    (k : ZMod n) (x : Fin n → G) : Fin n → G :=
  fun i => x ⟨(i.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩

end MetaMathlibExt
end
