import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ZPlusModules
import Lemma.Category.Atlas.v1.TensorCategories.code.ZPlusModules


/--
[Lemma_2_8_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_8_5.lean)
-/
@[path]
lemma Lemma_2_8_5
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRing ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModule R κ}
-- given
  (hindec : M.IsIndecomposable)
  (hexact : M.IsExact) :
-- imply
  M.IsIrreducible :=
-- proof
  M.lemma_2_8_5 hindec hexact


-- created on 2026-10-23
