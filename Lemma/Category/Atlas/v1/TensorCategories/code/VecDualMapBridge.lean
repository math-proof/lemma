import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.VecDualMapBridge
open CategoryTheory MonoidalCategory Module


/--
[FGModuleCat.rightAdjointMate_hom_eq_dualMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecDualMapBridge.lean)
-/
@[path]
private lemma rightAdjointMate_hom_eq_dualMap_eq
  {k : Type u}
  [Field k]
  {V W : FGModuleCat.{u} k}
  {f : V ⟶ W} :
-- imply
  (rightAdjointMate f).hom.hom = f.hom.hom.dualMap := by
-- proof
  apply FGModuleCat.rightAdjointMate_hom_eq_dualMap k f


-- created on 2026-10-23
