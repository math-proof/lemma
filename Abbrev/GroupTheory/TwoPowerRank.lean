/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.GroupTheory.TwoPowerRank
/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/


namespace AbelianGroup

/-- For positive `j`, the additive quotient `2^(j-1) A / 2^j A`. -/
abbrev higherTwoPowerLayer (A : Type*) [AddCommGroup A] (j : ℕ) : Type _ :=
  twoPowerImage A (j - 1) ⧸
    ((twoPowerImage A j).comap (twoPowerImage A (j - 1)).subtype).toAddSubgroup

end AbelianGroup
