/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.NicholsZoeller
import Lemma.Category.Atlas.v1.TensorCategories.code.NicholsZoeller
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctorProjective
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective

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
