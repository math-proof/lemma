import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TensorCategories.code.VecCategoricalFusionData
open CategoryTheory MonoidalCategory Module TensorProduct VecCategoricalFusionData


/--
[vec_hom_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecCategoricalFusionData.lean)
-/
@[path]
private lemma vec_hom_finrank_eq
  {k : Type u}
  [Field k] :
-- imply
  finrank k (FGModuleCat.of k k ⟶ (FGModuleCat.of k k ⊗ FGModuleCat.of k k)) = 1 := by
-- proof
  apply VecCategoricalFusionData.vec_hom_finrank k


-- created on 2026-10-23
