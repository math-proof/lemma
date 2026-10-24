import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra


/--
[antipode_injective_of_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AntipodeBijective/Injective.lean)
-/
@[path]
lemma antipode_injective_of_finiteDimensional
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [HopfAlgebra k H]
  [FiniteDimensional k H] :
-- imply
  Function.Injective (⇑(HopfAlgebra.antipode k) : H → H) :=
-- proof
  (HopfAlgebra.antipode_bijective k H).1


-- created on 2026-10-23
