/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.NicholsZoeller
import Lemma.Category.Atlas.v1.TensorCategories.code.NicholsZoeller
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctorProjective
import Class.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective.Part3
set_option maxHeartbeats 400000


noncomputable section

universe u v v₁ w

section NicholsZoellerFull

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]

/-- The full Hopf subalgebra `H ⊆ H`: the top subalgebra carries the antipode trivially. -/
def SubHopfAlgebra.full : SubHopfAlgebra k H where
  toSubalgebra := ⊤
  antipode_mem := fun _ => Algebra.mem_top

variable [FiniteDimensional k H]

/-- The ring homomorphism `H → ↥(full H)` sending each element to itself viewed as a
member of the full Hopf subalgebra. -/
def SubHopfAlgebra.full_inclRingHom : H →+* ↥(SubHopfAlgebra.full k H) where
  toFun h := ⟨h, Algebra.mem_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ring homomorphism `↥(full H) → H` extracting the underlying element. -/
def SubHopfAlgebra.full_valRingHom : ↥(SubHopfAlgebra.full k H) →+* H :=
  (SubHopfAlgebra.full k H).toSubalgebra.val.toRingHom

end NicholsZoellerFull
end
