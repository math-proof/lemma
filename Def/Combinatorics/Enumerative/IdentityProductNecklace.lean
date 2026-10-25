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


section

namespace MetaMathlibExt

/-- Rotation of a tuple by `k` positions (forward shift of indices). -/
def rotShift (G : Type*) (n : ℕ) [NeZero n]
    (k : ZMod n) (x : Fin n → G) : Fin n → G :=
  fun i => x ⟨(i.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩

end MetaMathlibExt
end
