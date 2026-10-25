import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part5
open CategoryTheory GroupoidMultitensor


namespace GroupoidMultitensor

/--
[FiniteGroupoidData.id_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean)
-/
@[path]
lemma FiniteGroupoidData.id_injective
  {G : FiniteGroupoidData} :
-- imply
  Function.Injective G.id := by
-- proof
  intro x y h
  have hx := G.src_id x
  have hy := G.src_id y
  rw [h] at hx
  rw [← hx, hy]

end GroupoidMultitensor

namespace GroupoidMultitensor

/--
[FiniteGroupoidData.unitComponents_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean)
-/
@[path]
lemma FiniteGroupoidData.unitComponents_card
  {G : FiniteGroupoidData} :
-- imply
  G.unitComponents.card = Fintype.card G.Obj := by
-- proof
  simp [unitComponents, Finset.card_image_of_injective _ G.id_injective]

end GroupoidMultitensor

namespace GroupoidMultitensor

/--
[FiniteGroupoidData.finrank_endUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean)
-/
@[path]
lemma FiniteGroupoidData.finrank_endUnit
  {G : FiniteGroupoidData}
  {k : Type w}
  [Field k] :
-- imply
  Module.finrank k (G.EndUnit k) = Fintype.card G.Obj :=
-- proof
  Module.finrank_pi k

end GroupoidMultitensor

namespace GroupoidMultitensor

/--
[FiniteGroupoidData.endUnit_iso_k_iff_singleObject](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean)
-/
@[path]
lemma FiniteGroupoidData.endUnit_iso_k_iff_singleObject
  {G : FiniteGroupoidData}
  {k : Type w}
  [Field k] :
-- imply
  Module.finrank k (G.EndUnit k) = 1 ↔ G.IsSingleObject := by
-- proof
  unfold IsSingleObject
  rw [G.finrank_endUnit k]

end GroupoidMultitensor

namespace GroupoidMultitensor

/--
[FiniteGroupoidData.endUnit_dim_gt_one_of_multipleObjects](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean)
-/
@[path]
lemma FiniteGroupoidData.endUnit_dim_gt_one_of_multipleObjects
  {G : FiniteGroupoidData}
  {k : Type w}
  [Field k]
-- given
  (h : 1 < Fintype.card G.Obj) :
-- imply
  1 < Module.finrank k (G.EndUnit k) := by
-- proof
  rwa [G.finrank_endUnit k]

end GroupoidMultitensor


-- created on 2026-10-23
