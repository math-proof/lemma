import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.TwoPowerRank
open AbelianGroup


/--
[twoPowerImage_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean)
-/
@[path]
private lemma twoPowerImage_succ_le_eq
  [AddCommGroup A]
  {k : ℕ} :
-- imply
  twoPowerImage A (k + 1) ≤ twoPowerImage A k := by
-- proof
  apply AbelianGroup.twoPowerImage_succ_le A k

/--
[higherTwoPowerRank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean)
-/
@[path]
private lemma higherTwoPowerRank_eq_eq
  [AddCommGroup A] [Finite A]
  {j : ℕ}
-- given
  (hj : 0 < j) :
-- imply
  letI : Fact (0 < j) := by
-- proof
  apply AbelianGroup.higherTwoPowerRank_eq A j hj

/--
[fourRank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean)
-/
@[path]
private lemma fourRank_eq_eq
  [AddCommGroup A] [Finite A] :
-- imply
  letI : Fact (0 < 2) := by
-- proof
  apply AbelianGroup.fourRank_eq A


-- created on 2026-10-20
