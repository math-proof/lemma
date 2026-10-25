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
import Instance.v1.Atlas.TensorCategories.code.ConcreteInstances
set_option maxHeartbeats 400000


noncomputable section

universe u v v₁ w

section NicholsZoellerFull

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]

variable [FiniteDimensional k H]

/-- A semilinear equivalence between `H` and the full Hopf subalgebra `↥(full H)` with
respect to the inclusion ring homomorphism — used to transfer module-theoretic structure. -/
def SubHopfAlgebra.fullSemilinearEquiv :
    @LinearEquiv H ↥(SubHopfAlgebra.full k H)
      inferInstance inferInstance
      (SubHopfAlgebra.full_inclRingHom k H) (SubHopfAlgebra.full_valRingHom k H)
      (SubHopfAlgebra.full_inclValPair k H) (SubHopfAlgebra.full_valInclPair k H)
      H H
      inferInstance inferInstance
      inferInstance inferInstance
    where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    show r * x = (⟨r, Algebra.mem_top⟩ : ↥(SubHopfAlgebra.full k H)) • x
    simp [Subalgebra.smul_def]

end NicholsZoellerFull
end
