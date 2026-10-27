import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SnakeLemma
open CategoryTheory CategoryTheory.Limits SnakeLemma


namespace SnakeLemma

/--
[snake_lemma_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SnakeLemma.lean)
-/
@[path]
lemma snake_lemma_exact
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {S : ShortComplex.SnakeInput C} :
-- imply
  S.composableArrows.Exact :=
-- proof
  S.snake_lemma

end SnakeLemma


-- created on 2026-10-23
