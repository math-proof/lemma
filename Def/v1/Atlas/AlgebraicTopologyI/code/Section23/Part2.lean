/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section23.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.Order.Directed
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Flat.Localization
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section23


namespace DirectLimitTensor

open TensorProduct Module Module.DirectLimit

variable {R : Type*} [CommSemiring R]

variable {ι : Type*} [DecidableEq ι] [Preorder ι]

variable {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable (N : Type*) [AddCommMonoid N] [Module R N]

/-- Proposition 23.10. For a directed system of `R`-modules `G : ι → Mod_R` and an `R`-module
`N`, the tensor product commutes with direct limits: there is a natural isomorphism
`(lim→ G_i) ⊗_R N ≃ lim→ (G_i ⊗_R N)`. -/
noncomputable def directLimitTensorIso :
    Module.DirectLimit G f ⊗[R] N ≃ₗ[R]
      Module.DirectLimit (fun i => G i ⊗[R] N)
        (fun i j h => LinearMap.rTensor N (f i j h)) :=
  TensorProduct.directLimitLeft f N

end DirectLimitTensor

namespace DirectLimitCharacterization

open Module.DirectLimit

variable {R : Type*} [Ring R]
  {ι : Type*} [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι]
  {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
  [DirectedSystem G fun i j h => f i j h]
  {L : Type*} [AddCommGroup L] [Module R L]
  (g : ∀ i, G i →ₗ[R] L)
  (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

/-- The `n`-th singular homology of a space `X` with rational coefficients, packaged as an
object of `AddCommGrpCat`. -/
noncomputable def SingularHomologyGroupQ (n : ℕ) (X : Type) [TopologicalSpace X] :
    AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℚ)).obj (TopCat.of X)


/-- Promote an `AddEquiv` between objects of `AddCommGrpCat` to a categorical isomorphism. -/
noncomputable def AddCommGrpCat.isoOfAddEquiv' {A B : AddCommGrpCat}
    (e : A ≃+ B) : A ≅ B where
  hom := AddCommGrpCat.ofHom e.toAddMonoidHom
  inv := AddCommGrpCat.ofHom e.symm.toAddMonoidHom
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

end DirectLimitCharacterization
