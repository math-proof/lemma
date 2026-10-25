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
import Def.v1.Atlas.TensorCategories.code.ConcreteInstances
set_option maxHeartbeats 400000


noncomputable section

universe u v v₁ w

section NicholsZoellerFull

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]

variable [FiniteDimensional k H]

/-- `full_inclRingHom` and `full_valRingHom` form a `RingHomInvPair`. -/
instance SubHopfAlgebra.full_inclValPair :
    RingHomInvPair (SubHopfAlgebra.full_inclRingHom k H)
      (SubHopfAlgebra.full_valRingHom k H) where
  comp_eq := by ext x; rfl
  comp_eq₂ := by ext ⟨x, _⟩; rfl

/-- The reverse `RingHomInvPair` instance: `val` then `incl` is the identity. -/
instance SubHopfAlgebra.full_valInclPair :
    RingHomInvPair (SubHopfAlgebra.full_valRingHom k H)
      (SubHopfAlgebra.full_inclRingHom k H) where
  comp_eq := by ext ⟨x, _⟩; rfl
  comp_eq₂ := by ext x; rfl

end NicholsZoellerFull
end
