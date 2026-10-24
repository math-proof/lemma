import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.VecSphericalConcrete
open CategoryTheory MonoidalCategory Module Category


/--
[vecPivotalDim_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSphericalConcrete.lean)
-/
@[path]
private lemma vecPivotalDim_apply_one_eq
  {k : Type u}
  [Field k]
  {V : FGModuleCat.{u} k} :
-- imply
  (vecPivotalDim k V).hom.hom 1 = (Module.finrank k V : k) := by
-- proof
  apply vecPivotalDim_apply_one k V

/--
[vec_spherical_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSphericalConcrete.lean)
-/
@[path]
private lemma vec_spherical_condition_eq
  {k : Type u}
  [Field k]
  {V : FGModuleCat.{u} k} :
-- imply
  vecPivotalDim k V = vecPivotalDim k (Vᘁ) := by
-- proof
  apply vec_spherical_condition k V


-- created on 2026-10-23
