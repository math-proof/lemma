/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section23.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.Order.Directed
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Flat.Localization

namespace HomTensorAdjunction

open TensorProduct

/-- Lemma 23.1 (Hom–tensor adjunction). The natural map
`Hom(L, Hom(M, N)) → Hom(L ⊗ M, N)` is an isomorphism, witnessed here as an `R`-linear
equivalence between `L →ₗ[R] M →ₗ[R] N` and `L ⊗[R] M →ₗ[R] N`. -/
noncomputable def homTensorEquiv
    (R : Type*) [CommSemiring R]
    (L M N : Type*) [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
    [Module R L] [Module R M] [Module R N] :
    (L →ₗ[R] M →ₗ[R] N) ≃ₗ[R] (L ⊗[R] M →ₗ[R] N) :=
  TensorProduct.lift.equiv (RingHom.id R) L M N

end HomTensorAdjunction

namespace DirectedSystems

/-- Definition 23.2. A poset `(I, ≤)` is directed if for every `i, j ∈ I` there is some
`k ∈ I` with `i ≤ k` and `j ≤ k`. -/
abbrev DirectedPoset (I : Type*) [Preorder I] : Prop :=
  IsDirected I (· ≤ ·)

open CategoryTheory

/-- Definition 23.4. An `I`-directed system in a category `C` (for `I` a directed poset)
is a functor `I ⥤ C`, i.e. objects `X_i` together with coherent maps `X_i → X_j` whenever
`i ≤ j`. -/
abbrev DirectedSystemFunctor (I : Type*) [Preorder I] [IsDirected I (· ≤ ·)]
    (C : Type*) [Category C] :=
  Functor I C

section CategoricalDirectLimit

open CategoryTheory CategoryTheory.Limits

/-- Definition 23.8 (categorical form). The direct limit `lim→ F` of a diagram `F : J ⥤ C`
is the colimit of `F`, i.e. the initial cocone under `F`. -/
noncomputable abbrev CategoricalDirectLimit {J : Type*} [Category J] {C : Type*} [Category C]
    (F : J ⥤ C) [HasColimit F] : C :=
  colimit F

end CategoricalDirectLimit

/-- Definition 23.8 (module form). The direct limit of a directed system of `R`-modules,
realized as Mathlib's `Module.DirectLimit` of the modules `G i` along the structure maps `f`. -/
abbrev DirectLimit
    (R : Type*) [Semiring R]
    (ι : Type*) [Preorder ι] [DecidableEq ι]
    (G : ι → Type*) [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) : Type _ :=
  Module.DirectLimit G f

end DirectedSystems

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

end AlgebraicTopologyI


open CategoryTheory AlgebraicTopology TensorProduct in
/-- Auxiliary form of the universal-coefficient style identification used to derive
Corollary 23.14: singular homology with coefficients in `ℤ ⊗[ℤ] ℚ` agrees up to isomorphism
with integral homology tensored with `ℚ`. -/
namespace AlgebraicTopologyI

open CategoryTheory AlgebraicTopology TensorProduct

/-- Corollary 23.14. Rational singular homology agrees with integral singular homology
tensored with `ℚ`: `H_n(X; ℚ) ≅ H_n(X) ⊗ ℚ`. -/
end AlgebraicTopologyI
