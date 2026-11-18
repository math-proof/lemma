/- Port of Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances.
   Lemma original left in place. Not a reuse of Theorem.v1.VecInstances. -/

module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2

public section

open CategoryTheory MonoidalCategory Limits VecInstances


/--
[hasFiniteLength_vec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean)
-/
@[path]
public theorem hasFiniteLength_vec_eq
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
public theorem linearMap_eq_of_apply_one_eq
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
