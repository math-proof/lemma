import Mathlib
import sympy.Basic
import sympy.atlas.Order.BooleanAlgebra.StoneRepresentation
open MathlibExt.Order.BooleanAlgebra.StoneRepresentation


/--
[stone_representation_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/BooleanAlgebra/StoneRepresentation.lean)
-/
@[path]
private lemma stone_representation_theorem_eq
  {B : Type u} [BooleanAlgebra B] :
-- imply
  ∃ (X : Type u) (f : BoundedLatticeHom B (Set X)), Function.Injective f := by
-- proof
  apply MathlibExt.Order.BooleanAlgebra.StoneRepresentation.stone_representation_theorem


-- created on 2026-10-20
