import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Definition_1_22_2
open Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct


/--
[Definition_1_22_2_antipode](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_22_2.lean)
-/
@[path]
lemma Definition_1_22_2_antipode
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [HopfAlgebra k H] :
-- imply
  Definition_1_22_2 k H (HopfAlgebra.antipode k) :=
-- proof
  ⟨HopfAlgebra.mul_antipode_rTensor_comul, HopfAlgebra.mul_antipode_lTensor_comul⟩
section Definition_1_22_2_correspondence
variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [Bialgebra k H]


-- created on 2026-10-23
