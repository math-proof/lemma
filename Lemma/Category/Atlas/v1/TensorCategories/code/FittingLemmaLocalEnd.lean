import Mathlib
import sympy.Basic
import Class.v1.Atlas.TensorCategories.code.FittingLemmaLocalEnd
open CategoryTheory CategoryTheory.Limits


namespace CategoryTheory

/--
[endRing_isArtinian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingLemmaLocalEnd.lean)
-/
@[path]
lemma endRing_isArtinian
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear k C]
  {P : C}
  [FiniteDimensional k (End P)] :
-- imply
  IsArtinianRing (End P) :=
-- proof
  isArtinian_of_tower k (inferInstance : IsArtinian k (End P))

end CategoryTheory


-- created on 2026-10-23
