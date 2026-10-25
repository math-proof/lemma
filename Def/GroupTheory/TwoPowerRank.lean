/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finrank
/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/


namespace AbelianGroup

/-- The subgroup `2^k A` of an additive commutative group. -/
def twoPowerImage (A : Type*) [AddCommGroup A] (k : ℕ) : Submodule ℤ A :=
  LinearMap.range (LinearMap.lsmul ℤ A (2 ^ k : ℤ))

end AbelianGroup
