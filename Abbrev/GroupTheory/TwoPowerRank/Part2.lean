/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.GroupTheory.TwoPowerRank.Part2
@[expose] public section

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
