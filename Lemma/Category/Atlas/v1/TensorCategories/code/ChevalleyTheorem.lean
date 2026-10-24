import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ChevalleyTheorem
open TensorProduct


/--
[MonoidAlgebra.instIsSemisimpleRing_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyTheorem.lean)
-/
@[path]
lemma MonoidAlgebra.instIsSemisimpleRing_of_finite
  {k : Type*}
  [Field k]
  [CharZero k]
  {G : Type*}
  [CommGroup G]
  [Finite G] :
-- imply
  IsSemisimpleRing (MonoidAlgebra k G) := by
-- proof
  have : NeZero (Nat.card G : k) := by
    constructor
    exact_mod_cast Nat.card_pos.ne'
  exact inferInstance

/--
[MonoidAlgebra.finiteDim_isSemisimpleModule_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyTheorem.lean)
-/
@[path]
lemma MonoidAlgebra.finiteDim_isSemisimpleModule_of_finite
  {k : Type*}
  [Field k]
  [CharZero k]
  {G : Type*}
  [CommGroup G]
  [Finite G]
  {M : Type*}
  [AddCommGroup M]
  [Module k M]
  [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]
  [Module.Finite k M] :
-- imply
  IsSemisimpleModule (MonoidAlgebra k G) M := by
-- proof
  have : NeZero (Nat.card G : k) := by
    constructor
    exact_mod_cast Nat.card_pos.ne'
  have : IsSemisimpleRing (MonoidAlgebra k G) := inferInstance
  exact IsSemisimpleRing.isSemisimpleModule


-- created on 2026-10-23
