import Mathlib
import sympy.Basic
open Function


/--
[antipode_bijective_of_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AntipodeBijective/Assembly.lean)
-/
@[path]
lemma antipode_bijective_of_finiteDimensional
  {K : Type*}
  [Field K]
  {H : Type*}
  [Ring H]
  [HopfAlgebra K H]
  [FiniteDimensional K H] :
-- imply
  Function.Bijective (⇑(HopfAlgebra.antipode K) : H → H) :=
-- proof
  ⟨antipode_injective_of_finiteDimensional K H, (HopfAlgebra.antipode_bijective K H).2⟩


-- created on 2026-10-23
