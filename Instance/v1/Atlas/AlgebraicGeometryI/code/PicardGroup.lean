/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.PicardGroup
open TensorProduct

universe u


namespace InvertibleSheaves

/-- The tensor product of two invertible modules is invertible (Pic is closed under
multiplication). -/
instance invertible_tensor (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    (N : Type*) [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    Module.Invertible R (M ⊗[R] N) := inferInstance

/-- The dual of an invertible module is invertible: this gives inverses in Pic. -/
instance invertible_dual (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    Module.Invertible R (Module.Dual R M) := inferInstance

/-- R itself is invertible as an R-module, serving as the identity element of Pic. -/
instance invertible_self (R : Type u) [CommSemiring R] :
    Module.Invertible R R := inferInstance

/-- The Picard group of R is a commutative group under tensor product
(Corollary 19, Lecture 14/15). -/
noncomputable instance picardGroup_commGroup (R : Type u) [CommSemiring R] :
    CommGroup (CommRing.Pic R) := inferInstance

end InvertibleSheaves
