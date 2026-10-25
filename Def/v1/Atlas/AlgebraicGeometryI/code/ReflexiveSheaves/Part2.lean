/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Ideal.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.ReflexiveSheaves


noncomputable section

namespace ReflexiveSheaf

open Module

section TensorHomIdentity

/-- The natural identification `Hom_R(M, N) ≃ M^∨ ⊗ N` for a finitely-generated
free `M`, the basic dual-tensor-hom isomorphism for locally free sheaves. -/
def dualTensorHomLocallyFree (R : Type*) (M : Type*) (N : Type*)
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Free R M] [Module.Finite R M] :
    (M →ₗ[R] N) ≃ₗ[R] TensorProduct R (Module.Dual R M) N :=
  (dualTensorHomEquiv R M N).symm

end TensorHomIdentity

section RankOneDual

variable (R : Type*) [CommRing R]

/-- The ring of endomorphisms of the rank-one free module is isomorphic to `R`
itself, via evaluation at a basis vector. -/
def endRankOneEquiv : ((Fin 1 → R) →ₗ[R] (Fin 1 → R)) ≃ₗ[R] R :=
  (LinearEquiv.arrowCongr (LinearEquiv.funUnique (Fin 1) R R)
    (LinearEquiv.funUnique (Fin 1) R R)).trans (LinearMap.ringLmapEquivSelf R R R)

/-- The dual-tensor-hom contraction for the rank-one free module collapses to
the ring `R`. -/
def dualTensorRankOneIso :
    TensorProduct R (Module.Dual R (Fin 1 → R)) (Fin 1 → R) ≃ₗ[R] R :=
  (dualTensorHomEquiv R (Fin 1 → R) (Fin 1 → R)).trans (endRankOneEquiv R)

end RankOneDual
end ReflexiveSheaf
end
