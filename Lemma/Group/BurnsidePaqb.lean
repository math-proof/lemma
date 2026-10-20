import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb
open BurnsidePaqb


/--
[burnside_paqb_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb.lean)
-/
@[path]
private lemma burnside_paqb_zero_eq
  [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hcard : Fintype.card G = p ^ a * q ^ b) :
-- imply
  Group.IsSolvable G := by
-- proof
  apply BurnsidePaqb.burnside_paqb_zero p q a b hp hq hcard

/--
[burnside_paqb](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb.lean)
-/
@[path]
private lemma burnside_paqb_eq
  [Group G] [Fintype G]
  {p q a b : ℕ}
-- given
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hcard : Fintype.card G = p ^ a * q ^ b) :
-- imply
  Group.IsSolvable G := by
-- proof
  apply BurnsidePaqb.burnside_paqb p q a b hp hq hcard


-- created on 2026-10-20
