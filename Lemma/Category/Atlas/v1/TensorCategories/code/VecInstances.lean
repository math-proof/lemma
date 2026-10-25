import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
open CategoryTheory MonoidalCategory Limits VecInstances


/--
[hasFiniteLength_vec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean)
-/
@[path]
private lemma hasFiniteLength_vec_eq
  {k : Type u}
  [Field k]
  {X : Vec k} :
-- imply
  TensorCategories.HasFiniteLength X := by
-- proof
  apply VecInstances.hasFiniteLength_vec k X

/--
[linearMap_eq_of_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean)
-/
@[path]
private lemma linearMap_eq_of_apply_one_eq
  {k : Type u}
  [Field k]
  {f g : k →ₗ[k] k}
-- given
  (h : f 1 = g 1) :
-- imply
  f = g := by
-- proof
  apply VecInstances.linearMap_eq_of_apply_one k f g h


-- created on 2026-10-23
