/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace TensorChainComplex

variable (R : Type) [CommRing R]

/-- The tensor product of two chain complexes of $R$-modules, with the Leibniz
differential
$d(x \otimes y) = dx \otimes y + (-1)^{|x|} x \otimes dy$.
This is the algebraic side of the Künneth formula. -/
def tensorChainComplex
    (C D : ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  HomologicalComplex.tensorObj C D

/-- The canonical inclusion of the bidegree $(p,q)$ summand $C_p \otimes D_q$ into the
total complex $(C \otimes D)_n$ for $p + q = n$. -/
def ιTensorChainComplex
    (C D : ChainComplex (ModuleCat R) ℕ)
    (p q n : ℕ) (h : p + q = n) :
    (C.X p ⊗ D.X q) ⟶ (tensorChainComplex R C D).X n :=
  HomologicalComplex.ιTensorObj C D p q n h

/-- The index set of pairs $(p, q)$ of nonnegative integers with $p + q = n$, used to
index the bidegree summands of the total complex of a tensor product. -/
abbrev PairSum (n : ℕ) := { pq : ℕ × ℕ // pq.1 + pq.2 = n }

variable [IsPrincipalIdealRing R]

set_option linter.unusedSectionVars false in

/-- The category $\mathrm{ModuleCat}\,R$ of $R$-modules has projective resolutions; an
instance reused throughout the Tor / UCT / Künneth development. -/
instance moduleCat_hasProjectiveResolutions (R : Type) [Ring R] :
    HasProjectiveResolutions (ModuleCat.{0} R) := inferInstance

end FreeResolutions

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

/-- An augmented chain-complex-valued functor: a functor $\mathcal{C} \to \mathrm{Ch}_*$
together with an augmentation $F_0 \to T$ to a target functor $T : \mathcal{C} \to \mathrm{Ab}$.
This is the input data on which the acyclic models theorem operates. -/
structure AugChainComplexFunctor (𝒞 : Type u) [Category.{v} 𝒞] where
  chainFun : 𝒞 ⥤ HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ)
  target : 𝒞 ⥤ AddCommGrpCat.{v}
  augmentation :
    chainFun ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.down ℕ) 0 ⟶ target

/-- The degree-$n$ component of an augmented chain-complex functor as a functor
$\mathcal{C} \to \mathrm{Ab}$, obtained by composing with the evaluation functor at $n$. -/
def AugChainComplexFunctor.componentFun (F : AugChainComplexFunctor 𝒞) (n : ℕ) :
    𝒞 ⥤ AddCommGrpCat.{v} :=
  F.chainFun ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.down ℕ) n

/-- An augmented chain-complex functor is $\mathcal{M}$-exact (acyclic on models) if on
each model $M \in \mathcal{M}$ the augmented chain complex is exact: higher exactness in
positive degrees, surjectivity of the augmentation, and exactness at degree 0. This is
the acyclicity hypothesis in the acyclic models theorem. -/
def IsMExactAugmented (𝓜 : Set 𝒞) (F : AugChainComplexFunctor 𝒞) : Prop :=
  ∀ M ∈ 𝓜,
    (∀ n : ℕ, (F.chainFun.obj M).ExactAt (n + 1)) ∧
    Function.Surjective (F.augmentation.app M) ∧
    (F.chainFun.obj M).d 1 0 ≫ F.augmentation.app M = 0 ∧
    (∀ x : (F.chainFun.obj M).X 0, F.augmentation.app M x = 0 →
      ∃ y : (F.chainFun.obj M).X 1, (F.chainFun.obj M).d 1 0 y = x)

/-- The natural transformation $F_i \Rightarrow F_j$ induced by the differential
$d_{ij}$ of the underlying chain complex, viewed in the functor category. -/
def AugChainComplexFunctor.dNat (F : AugChainComplexFunctor 𝒞) (i j : ℕ) :
    F.componentFun i ⟶ F.componentFun j where
  app X := (F.chainFun.obj X).d i j
  naturality X Y f := by
    simp only [componentFun, Functor.comp_map, HomologicalComplex.eval_map]
    exact (F.chainFun.map f).comm i j

/-- The covering condition: a chain map $\varphi : F \to G$ between augmented
chain-complex functors covers a natural transformation $\theta : F_{\mathrm{aug}} \to G_{\mathrm{aug}}$
of targets iff the obvious square commutes on every object $X$. -/
def Covers (F G : AugChainComplexFunctor 𝒞)
    (φ : F.chainFun ⟶ G.chainFun) (θ : F.target ⟶ G.target) : Prop :=
  ∀ X : 𝒞, (φ.app X).f 0 ≫ G.augmentation.app X = F.augmentation.app X ≫ θ.app X

/-- A natural transformation between functors valued in chain complexes is a natural
chain-homotopy equivalence if there is a natural inverse and, on every object, the pair
$(\varphi_X, \psi_X)$ assembles into a `HomotopyEquiv`. -/
def IsNatChainHomotopyEquiv
    {F_star G_star : 𝒞 ⥤ HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ)}
    (φ : F_star ⟶ G_star) : Prop :=
  ∃ ψ : G_star ⟶ F_star, ∀ X : 𝒞,
    ∃ e : HomotopyEquiv (F_star.obj X) (G_star.obj X),
      e.hom = φ.app X ∧ e.inv = ψ.app X

/-- Two natural transformations of chain-complex functors are objectwise chain homotopic
if, for every $X \in \mathcal{C}$, the components $\Phi_X$ and $\Psi_X$ are chain
homotopic as ordinary chain maps. -/
def ObjectwiseHomotopic
    {F G : AugChainComplexFunctor 𝒞}
    (Φ Ψ : F.chainFun ⟶ G.chainFun) : Prop :=
  ∀ X : 𝒞, Nonempty (Homotopy (Φ.app X) (Ψ.app X))

/-- The shape of homotopy data used in the acyclic models uniqueness proof: a family of
natural transformations $s_n : F_n \to G_{n+1}$, evaluated at $X$ and re-indexed to match
the `ComplexShape.down ℕ` relation. -/
noncomputable def natTransHomotopyData
    {F G : AugChainComplexFunctor 𝒞}
    (s : ∀ n : ℕ, F.componentFun n ⟶ G.componentFun (n + 1))
    (X : 𝒞) :
    (i j : ℕ) → (ComplexShape.down ℕ).Rel j i →
      ((F.chainFun.obj X).X i ⟶ (G.chainFun.obj X).X j) :=
  fun i j (hij : i + 1 = j) => hij ▸ ((s i).app X)

/-- The objectwise chain homotopy between $\Phi_1$ and $\Phi_2$ associated to a family of
natural transformations $s_n : F_n \to G_{n+1}$ satisfying the chain-homotopy identity
$\Phi_1 - \Phi_2 = d \circ s + s \circ d$ as a null-homotopic map. -/
noncomputable def natTransHomotopy
    {F G : AugChainComplexFunctor 𝒞}
    (Φ₁ Φ₂ : F.chainFun ⟶ G.chainFun)
    (s : ∀ n : ℕ, F.componentFun n ⟶ G.componentFun (n + 1))
    (heq : ∀ X : 𝒞,
      Φ₁.app X - Φ₂.app X = Homotopy.nullHomotopicMap' (natTransHomotopyData s X))
    (X : 𝒞) : Homotopy (Φ₁.app X) (Φ₂.app X) :=
  Homotopy.equivSubZero.symm (by
    rw [heq]
    exact Homotopy.nullHomotopy' (natTransHomotopyData s X))

/-- Acyclic models yields a natural chain-homotopy equivalence: if $F$ and $G$ are both
$\mathcal{M}$-free and $\mathcal{M}$-exact on a common family of models, then any natural
transformation $\varphi : F \to G$ covering an isomorphism of augmentations is a natural
chain-homotopy equivalence. -/
end AcyclicModels

/-- The $n$-th singular homology of a space $X$ with coefficients in the ring $R$
(viewed as the regular $R$-module), as an object of $\mathrm{ModuleCat}\,R$. -/
def singularHomologyMod (n : ℕ) (X : TopCat.{0}) : ModuleCat R :=
  ((singularHomologyFunctor (ModuleCat R) n).obj (ModuleCat.of R R)).obj X

/-- The induced map on $n$-th singular homology with $R$ coefficients of a continuous map
$f : X \to Y$. -/
def singularHomologyModMap (n : ℕ) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularHomologyMod R n X ⟶ singularHomologyMod R n Y :=
  ((singularHomologyFunctor (ModuleCat R) n).obj (ModuleCat.of R R)).map f

/-- The tensor term in the topological Künneth short exact sequence: the direct sum
$\bigoplus_{p+q=n} H_p(X; R) \otimes_R H_q(Y; R)$. -/
def kunnethTensorTerm (n : ℕ) (X Y : TopCat.{0}) : ModuleCat R :=
  ∐ fun (pq : { pq : ℕ × ℕ // pq.1 + pq.2 = n }) =>
    singularHomologyMod R pq.1.1 X ⊗ singularHomologyMod R pq.1.2 Y

/-- The Tor term in the topological Künneth short exact sequence: the direct sum
$\bigoplus_{p+q=n-1} \mathrm{Tor}_1^R(H_p(X; R), H_q(Y; R))$. -/
def kunnethTorTerm (n : ℕ) (X Y : TopCat.{0}) : ModuleCat R :=
  ∐ fun (pq : { pq : ℕ × ℕ // pq.1 + pq.2 + 1 = n }) =>
    ((Tor (ModuleCat R) 1).obj (singularHomologyMod R pq.1.1 X)).obj
      (singularHomologyMod R pq.1.2 Y)

/-- The singular chain complex of a topological space with coefficients in $R$ is free in
each degree, since it is the free $R$-module on the set of singular simplices. -/
end KunnethTopological
