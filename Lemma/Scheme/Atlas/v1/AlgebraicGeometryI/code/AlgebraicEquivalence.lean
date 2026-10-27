import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence.Part4
open AlgebraicEquivalence AlgebraicEquivalence.CartierDivisorGroup
open AlgebraicGeometry CategoryTheory Limits


namespace AlgebraicEquivalence.CartierDivisorGroup

/--
[pullback_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean)
-/
@[path]
lemma pullback_comp
  {X Y Z : Scheme.{u}}
  {f : X ⟶ Y}
  {g : Y ⟶ Z}
  {D : CartierDivisorGroup Z} :
-- imply
  pullback (f ≫ g) D = pullback f (pullback g D) := by
-- proof
  funext x
  simp [pullback]

end AlgebraicEquivalence.CartierDivisorGroup

namespace AlgebraicEquivalence.CartierDivisorGroup

/--
[pullback_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean)
-/
@[path]
lemma pullback_id
  {X : Scheme.{u}}
  {D : CartierDivisorGroup X} :
-- imply
  pullback (𝟙 X) D = D := by
-- proof
  funext x
  simp [pullback]

end AlgebraicEquivalence.CartierDivisorGroup


-- created on 2026-10-23
