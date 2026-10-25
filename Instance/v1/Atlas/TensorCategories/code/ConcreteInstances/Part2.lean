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
import Def.v1.Atlas.TensorCategories.code.ConcreteInstances.Part2
set_option maxHeartbeats 400000


noncomputable section

universe u v v₁ w

section NicholsZoellerFull

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]

variable [FiniteDimensional k H]

/-- Nichols-Zoeller freeness instance for the trivial inclusion `H ⊆ H`: `H` is free
of rank one over itself, with `finrank` dividing trivially. -/
instance nicholsZoellerFull :
    NicholsZoellerFreeness k H (SubHopfAlgebra.full k H) where
  free := Module.Free.of_equiv (SubHopfAlgebra.fullSemilinearEquiv k H)
  finite := by
    constructor
    refine ⟨{1}, ?_⟩
    rw [eq_top_iff]
    intro h _
    have : h = (⟨h, Algebra.mem_top⟩ : ↥(SubHopfAlgebra.full k H)) • (1 : H) := by
      simp [Subalgebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton.mpr rfl)))
  finrank_dvd := by
    have h : Module.finrank k (SubHopfAlgebra.full k H) = Module.finrank k H := by
      exact LinearEquiv.finrank_eq (Subalgebra.topEquiv (R := k) (A := H)).toLinearEquiv
    rw [h]

end NicholsZoellerFull

namespace CategoryTheory

section IdentityFunctor

open Category MonoidalCategory

variable (k : Type w) [Field k]
  (C : Type u) [Category.{v₁} C] [MonoidalCategory C] [Abelian C]

/-- The identity functor on `C` is surjective: every object is a subquotient of itself
via the identity morphism. -/
instance identityIsSurjective : Functor.IsSurjective (𝟭 C) where
  surj Y := by
    refine ⟨Y, Y, 𝟙 Y, 𝟙 Y, ?_, ?_⟩
    · exact instMonoId Y
    · exact instEpiId Y

/-- The identity functor is additive. -/
instance identityAdditive : (𝟭 C).Additive where
  map_add := fun {_ _} _ _ => rfl

/-- The identity functor preserves monomorphisms. -/
instance identityPreservesMono : (𝟭 C).PreservesMonomorphisms where
  preserves {_ _} _ hf := hf

/-- The identity functor preserves epimorphisms. -/
instance identityPreservesEpi : (𝟭 C).PreservesEpimorphisms where
  preserves {_ _} _ hf := hf

/-- The identity functor on a `k`-linear abelian monoidal category is a quasi-tensor
functor. -/
instance identityQuasiTensorFunctor [Linear k C] :
    QuasiTensorFunctor k C C where
  F := 𝟭 C
  monoidal := inferInstance
  additive := identityAdditive C
  preservesMono := identityPreservesMono C
  preservesEpi := identityPreservesEpi C

/-- The identity functor is a surjective quasi-tensor functor. -/
instance identitySurjectiveQuasiTensorFunctor [Linear k C] :
    SurjectiveQuasiTensorFunctor k C C where
  surjective := identityIsSurjective C

end IdentityFunctor
end CategoryTheory
end
