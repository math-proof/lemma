/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

module

public import Mathlib.Data.Fintype.Basic
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.SuccPred
public import Theorem.GameTheory.SocialChoice.Arrow

@[expose] public section

section

namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-- Rank function putting `x` first, then `y`, then `z`, then everything else. -/
noncomputable def rank3 {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z w : Alt) : ℕ :=
  if w = x then 0 else if w = y then 1 else if w = z then 2 else 3 + baseRank (Alt := Alt) w

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
