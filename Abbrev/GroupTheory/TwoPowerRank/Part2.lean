/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.GroupTheory.TwoPowerRank.Part2
/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/


namespace AbelianGroup

/-- The `4`-rank is the `F₂`-dimension of `2A / 4A`. -/
noncomputable abbrev fourRank (A : Type*) [AddCommGroup A] [Finite A] : ℕ :=
  higherTwoPowerRank A 2 (by norm_num)

end AbelianGroup
