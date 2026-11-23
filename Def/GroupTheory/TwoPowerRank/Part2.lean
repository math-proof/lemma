/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Instance.GroupTheory.TwoPowerRank

@[expose] public section

/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/


namespace AbelianGroup

/-- For positive `j`, the `2^j`-rank of a finite abelian group `A` is the
`F₂`-dimension of `2^(j-1) A / 2^j A`. -/
noncomputable def higherTwoPowerRank (A : Type*) [AddCommGroup A] [Finite A]
    (j : ℕ) (hj : 0 < j) : ℕ :=
  letI : Fact (0 < j) := ⟨hj⟩
  Module.finrank (ZMod 2) (higherTwoPowerLayer A j)

end AbelianGroup
