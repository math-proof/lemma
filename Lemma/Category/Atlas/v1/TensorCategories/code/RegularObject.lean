import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.RegularObject
open FiniteTensorCategoryFPData


namespace FiniteTensorCategoryFPData

/--
[regularObject_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean)
-/
@[path]
lemma regularObject_coeff
  {D : FiniteTensorCategoryFPData}
  {i : D.I} :
-- imply
  D.regularObject.coeff i = D.fpDimSimple i := by
-- proof
  classical
  simp [regularObject, FormalProjectiveSum.coeff, FormalProjectiveSum.basis, Finsupp.single_apply]

end FiniteTensorCategoryFPData

namespace FiniteTensorCategoryFPData

/--
[fpdimRegularObject_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean)
-/
@[path]
lemma fpdimRegularObject_eq
  {D : FiniteTensorCategoryFPData} :
-- imply
  D.fpdimRegularObject = ∑ i : D.I, D.fpDimSimple i * D.fpDimProjCover i := by
-- proof
  simp [fpdimRegularObject, FormalProjectiveSum.fpdim]

end FiniteTensorCategoryFPData


-- created on 2026-10-23
