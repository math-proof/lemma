/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section25

@[expose] public section

open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace AcyclicModels

universe u v

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **Definition 25.7 ($\mathcal{M}$-epi)**. A natural transformation $\eta : F \to G$
between functors $\mathcal{C} \to \mathrm{Ab}$ is $\mathcal{M}$-epi if its component
$\eta_M : F(M) \to G(M)$ is surjective for every $M$ in the family of models
$\mathcal{M} \subseteq \mathcal{C}$. -/
def IsMEpi (𝓜 : Set 𝒞) {F G : 𝒞 ⥤ AddCommGrpCat.{v}} (η : F ⟶ G) : Prop :=
  ∀ M ∈ 𝓜, Function.Surjective (η.app M)

/-- **Definition 25.7 ($\mathcal{M}$-exact)**. A sequence
$G' \xrightarrow{\eta} G \xrightarrow{\psi} G''$ of functors $\mathcal{C} \to \mathrm{Ab}$
is $\mathcal{M}$-exact if, on every model $M \in \mathcal{M}$, the composite is zero and
the image of $\eta_M$ equals the kernel of $\psi_M$. -/
def IsMExact (𝓜 : Set 𝒞) {G' G G'' : 𝒞 ⥤ AddCommGrpCat.{v}}
    (η : G' ⟶ G) (ψ : G ⟶ G'') : Prop :=
  ∀ M ∈ 𝓜, (∀ y : G'.obj M, ψ.app M (η.app M y) = 0) ∧
            (∀ x : G.obj M, ψ.app M x = 0 → ∃ y : G'.obj M, η.app M y = x)

/-- The free-abelian-coyoneda functor at a model $M$: the composite of $\mathrm{Hom}(M, -)$
with the free abelian group functor, sending $X$ to $\mathbb{Z}\langle \mathrm{Hom}(M, X) \rangle$.
This is the basic building block of an $\mathcal{M}$-free functor. -/
def freeAbelianCoyoneda (M : 𝒞) : 𝒞 ⥤ AddCommGrpCat.{v} :=
  coyoneda.obj (Opposite.op M) ⋙ AddCommGrpCat.free

/-- **Definition 25.4 ($\mathcal{M}$-free)**. A functor $F : \mathcal{C} \to \mathrm{Ab}$
is $\mathcal{M}$-free if it is naturally isomorphic to a direct sum of free-abelian-coyoneda
functors indexed by some family of models in $\mathcal{M}$. Such functors lift against
$\mathcal{M}$-epis. -/
@[simp]
def IsMFree (𝓜 : Set 𝒞) (F : 𝒞 ⥤ AddCommGrpCat.{v}) : Prop :=
  ∃ (ι : Type v) (models : ι → 𝒞),
    (∀ i, models i ∈ 𝓜) ∧
    Nonempty (F ≅ ∐ (fun i => freeAbelianCoyoneda (models i)))

/-- The natural transformation $\mathbb{Z}\langle \mathrm{Hom}(M, -) \rangle \to G'$
classified by an element $c \in G'(M)$: it sends a morphism $\varphi : M \to X$ to
$G'(\varphi)(c)$. This is the universal property of the free-abelian-coyoneda functor. -/
def liftNatTrans {M : 𝒞} {G' : 𝒞 ⥤ AddCommGrpCat.{v}} (c : G'.obj M) :
    freeAbelianCoyoneda M ⟶ G' where
  app X := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun φ => (ConcreteCategory.hom (G'.map φ)) c))
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext; apply FreeAbelianGroup.lift_ext; intro φ
    dsimp [freeAbelianCoyoneda]
    erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
    change (ConcreteCategory.hom (G'.map ((yoneda.map g).app (Opposite.op M) φ))) c =
      (ConcreteCategory.hom (G'.map g)) ((ConcreteCategory.hom (G'.map φ)) c)
    simp only [yoneda_map_app]; rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]

end AcyclicModels
end
