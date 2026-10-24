/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section5
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section11
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple

open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI

open Set in
/-- **Definition 10.1 (Excisive triple).** *The triple `(X, A, U)` is **excisive** when
`closure U ⊆ interior A`, i.e. the closure of `U` lies in the topological interior of `A`.*

This is the hypothesis under which the excision theorem (Theorem 10.2) asserts that the
inclusion `(X ∖ U, A ∖ U) → (X, A)` induces an isomorphism on relative homology. -/
def IsExcisive (X : Type*) [TopologicalSpace X] (A U : Set X) : Prop :=
  closure U ⊆ interior A

namespace Excision

open AlgebraicTopology

noncomputable section

/-- The singular chain complex functor with integer coefficients,
`X ↦ C_*(X; \mathbb{Z})`. -/
abbrev singularChainZ : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The continuous inclusion `A ↪ X` of a subspace, as a morphism in `TopCat`. -/
def subspaceTopInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The chain map `C_*(A; ℤ) → C_*(X; ℤ)` induced by the subspace inclusion `A ↪ X`. -/
def subspaceChainInclusion (X : Type) [TopologicalSpace X] (A : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ singularChainZ.obj (TopCat.of X) :=
  singularChainZ.map (subspaceTopInclusion A)

/-- The *relative singular chain complex* `C_*(X, A; ℤ) := C_*(X) / C_*(A)`, defined as the
cokernel of the chain inclusion `C_*(A) ↪ C_*(X)`. -/
def relativeSingularChainComplex (X : Type) [TopologicalSpace X] (A : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (subspaceChainInclusion X A)

/-- The `n`-th *relative singular homology group* `H_n(X, A; ℤ)`, defined as the `n`-th
homology of the relative singular chain complex `C_*(X, A)`. -/
def RelativeSingularHomologyGroup (n : ℕ) (X : Type) [TopologicalSpace X] (A : Set X) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).obj
    (relativeSingularChainComplex X A)

variable (X : Type) [TopologicalSpace X] (A U : Set X)

/-- The continuous inclusion `A ∖ U ↪ A` obtained by viewing `A \ U` first as a subset of
`X \ U` and then forgetting the complement. -/
def excisedSubsetToSubspace :
    TopCat.of (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- The continuous inclusion `X ∖ U ↪ X`. -/
def complementInclusion :
    TopCat.of (Uᶜ : Set X) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Commutativity of the square `(A ∖ U) ↪ (X ∖ U); (A ∖ U) ↪ A` with `(X ∖ U) ↪ X; A ↪ X`,
which is what makes the excision pair-inclusion a well-defined morphism of pairs. -/
lemma excision_square_comm :
    subspaceTopInclusion (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ≫
      complementInclusion X U =
    excisedSubsetToSubspace X A U ≫ subspaceTopInclusion A := by
  ext ⟨⟨_, _⟩, _⟩; rfl

/-- The chain map between relative chain complexes
`C_*(X ∖ U, A ∖ U) → C_*(X, A)` induced by the pair inclusion. Excision asserts that this
map is a quasi-isomorphism whenever `(X, A, U)` is excisive. -/
def excisionRelativeChainMap :
    relativeSingularChainComplex (Uᶜ : Set X) (Subtype.val ⁻¹' A) ⟶
    relativeSingularChainComplex X A :=
  cokernel.map _ _
    (singularChainZ.map (excisedSubsetToSubspace X A U))
    (singularChainZ.map (complementInclusion X U))
    (by
      show singularChainZ.map _ ≫ singularChainZ.map _ =
        singularChainZ.map _ ≫ singularChainZ.map _
      rw [← singularChainZ.map_comp, ← singularChainZ.map_comp, excision_square_comm])

/-- The induced map on degree-`n` relative homology
`H_n(X ∖ U, A ∖ U) → H_n(X, A)` coming from the excision chain map. -/
def excisionHomologyMap (n : ℕ) :
    RelativeSingularHomologyGroup n (Uᶜ : Set X) (Subtype.val ⁻¹' A) ⟶
    RelativeSingularHomologyGroup n X A :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (excisionRelativeChainMap X A U)

end

end Excision

namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- The *small chain complex* `C^{\{A, B\}}_*(X)` for the two-element cover `{A, B}`: the
image of the chain map `C_*(A) ⊕ C_*(B) → C_*(X)` sending a pair to the sum of its
components in `C_*(X)`. -/
def smallChainComplex (X : Type) [TopologicalSpace X] (A B : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  image (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

/-- The inclusion `C^{\{A, B\}}_*(X) ↪ C_*(X)` of the small chain complex into the full
singular chain complex (the canonical image inclusion). -/
def smallChainInclusion (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainComplex X A B ⟶ singularChainZ.obj (TopCat.of X) :=
  image.ι _


/-- The inclusion of small singular chains into all singular chains is a monomorphism. -/
instance smallSingularInclusion_mono (X : Type) [TopologicalSpace X]
    (𝒜 : Set (Set X)) : Mono (LocalityPrinciple.smallSingularInclusion (TopCat.of X) 𝒜) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact ConcreteCategory.mono_of_injective _
    (LocalityPrinciple.smallSingularInclusion_injective (TopCat.of X) 𝒜 i)


/-- The canonical strong epimorphism `C_*(A) ⊕ C_*(B) ↠ C^{\{A, B\}}_*(X)` from the
biproduct to the small singular chain complex for the two-element cover `{A, B}`. -/
def smallChainInclusionA (X : Type) [TopologicalSpace X] (A B : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ smallChainComplex X A B :=
  biprod.inl ≫ factorThruImage (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

/-- Compatibility: the small-complex factorization of `C_*(A) ↪ C_*(X)` composed with the
inclusion of the small complex into `C_*(X)` recovers the original inclusion. -/
lemma smallChainInclusionA_comp_ι (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainInclusionA X A B ≫ smallChainInclusion X A B =
    subspaceChainInclusion X A := by
  change (biprod.inl ≫ factorThruImage
    (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))) ≫
    image.ι (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B)) = _
  rw [Category.assoc, image.fac, biprod.inl_desc]

/-- The defining short exact sequence of the relative chain complex
`0 → C_*(A) → C_*(X) → C_*(X, A) → 0`. -/
def bottomSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (subspaceChainInclusion X A)
    (cokernel.π (subspaceChainInclusion X A))

/-- The short exact sequence with `A`-chains, small chains, and their cokernel:
`0 → C_*(A) → C^{\{A, B\}}_*(X) → C^{\{A, B\}}_*(X) / C_*(A) → 0`. Used to compare with
`bottomSES` via the excision SES morphism. -/
def topSES (X : Type) [TopologicalSpace X] (A B : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (smallChainInclusionA X A B)
    (cokernel.π (smallChainInclusionA X A B))

/-- The morphism of short exact sequences from `topSES X A B` (small chains) to
`bottomSES X A` (full chains), with identity on `C_*(A)`, the small inclusion on the middle
term, and the induced map on cokernels on the right. -/
def excisionSESMorphism (X : Type) [TopologicalSpace X] (A B : Set X) :
    topSES X A B ⟶ bottomSES X A :=
  ShortComplex.Hom.mk
    (τ₁ := 𝟙 _)
    (τ₂ := smallChainInclusion X A B)
    (τ₃ := cokernel.map (smallChainInclusionA X A B)
      (subspaceChainInclusion X A)
      (𝟙 _) (smallChainInclusion X A B)
      (by rw [Category.id_comp, smallChainInclusionA_comp_ι]))
    (comm₁₂ := by
      show 𝟙 _ ≫ subspaceChainInclusion X A =
        smallChainInclusionA X A B ≫ smallChainInclusion X A B
      rw [Category.id_comp, smallChainInclusionA_comp_ι])
    (comm₂₃ := by
      show smallChainInclusion X A B ≫ cokernel.π (subspaceChainInclusion X A) =
        cokernel.π (smallChainInclusionA X A B) ≫ cokernel.map _ _ (𝟙 _) _ _
      rw [cokernel.π_desc])

/-- For a fixed abelian group `R`, the constant-coefficient `J ↦ ⊕_J R` functor sends
injective functions to monomorphisms. (Split mono when `J` is nonempty; zero object when
empty.) -/
lemma sigmaConst_map_mono_of_injective
    (J K : Type) (f : J → K) (hf : Function.Injective f)
    (R : AddCommGrpCat) :
    Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
  by_cases hJ : Nonempty J
  · exact (⟨Function.invFun f, Function.invFun_comp hf⟩ :
      SplitMono (show J ⟶ K from f)).map (sigmaConst.obj R) |>.mono
  · rw [not_nonempty_iff] at hJ
    exact (show IsZero ((sigmaConst.obj R).obj J) by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j; exact (hJ.false j).elim).mono _

/-- The total singular simplicial set functor `TopCat ⥤ SSet` preserves monomorphisms: an
injective continuous map is sent to a degreewise-injective map of simplicial sets. -/
instance toSSet_preservesMono : TopCat.toSSet.{0}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    intro n; rw [mono_iff_injective]
    intro σ₁ σ₂ h
    simp only [TopCat.toSSet, Presheaf.restrictedULiftYoneda, Functor.comp_map,
      Functor.whiskeringLeft, uliftYoneda] at h
    dsimp [Functor.whiskerLeft, yoneda, uliftFunctor] at h
    have h' : σ₁.down ≫ f = σ₂.down ≫ f := by
      have := congr_arg ULift.down h; simp at this; exact this
    exact ULift.ext _ _ ((cancel_mono f).mp h')

/-- The singular chain functor `C_*(-; ℤ) : TopCat ⥤ ChainComplex AddCommGrp` preserves
monomorphisms. -/
instance singularChainZ_preservesMono : singularChainZ.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))))
    apply sigmaConst_map_mono_of_injective
    haveI : Mono (TopCat.toSSet.map f) := Functor.map_mono TopCat.toSSet f
    have hmono_app : Mono ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))) :=
      (NatTrans.mono_iff_mono_app (TopCat.toSSet.map f)).mp this _
    exact (mono_iff_injective _).mp hmono_app


/-- The chain inclusion `C_*(A) ↪ C_*(X)` induced by `A ↪ X` is a monomorphism. -/
instance subspaceChainInclusion_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (subspaceChainInclusion X A) := by
  unfold subspaceChainInclusion
  haveI : Mono (subspaceTopInclusion A) := by
    rw [TopCat.mono_iff_injective]; exact Subtype.val_injective
  exact Functor.map_mono singularChainZ (subspaceTopInclusion A)

attribute [instance] subspaceChainInclusion_mono

/-- The map `C_*(A) → C^{\{A, B\}}_*(X)` is a monomorphism. -/
instance smallChainInclusionA_mono (X : Type) [TopologicalSpace X] (A B : Set X) :
    Mono (smallChainInclusionA X A B) :=
  mono_of_mono_fac (smallChainInclusionA_comp_ι X A B)

/-- The first map in `topSES X A B` is a monomorphism. -/
instance topSES_mono_f (X : Type) [TopologicalSpace X] (A B : Set X) :
    Mono (topSES X A B).f := smallChainInclusionA_mono X A B

/-- The second map in `topSES X A B` is an epimorphism (as a cokernel projection). -/
instance topSES_epi_g (X : Type) [TopologicalSpace X] (A B : Set X) :
    Epi (topSES X A B).g := by
  show Epi (cokernel.π (smallChainInclusionA X A B))
  infer_instance

/-- The first map in `bottomSES X A` is a monomorphism. -/
instance bottomSES_mono_f (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (bottomSES X A).f := subspaceChainInclusion_mono X A

/-- The second map in `bottomSES X A` is an epimorphism (as a cokernel projection). -/
instance bottomSES_epi_g (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (bottomSES X A).g := by
  show Epi (cokernel.π (subspaceChainInclusion X A))
  infer_instance

/-- The short complex `bottomSES X A` is short-exact. -/
lemma bottomSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (bottomSES X A).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

set_option maxHeartbeats 800000 in
/-- Compatibility condition exhibiting the kernel of `[φ, ψ] : 𝒜 ⊕ ℬ → 𝒳` as a span over `𝒳`
via the negated first projection and the second projection. Auxiliary lemma for the
abstract second isomorphism theorem. -/
lemma secondIso_kernel_pullback_cond :
    (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst (X := 𝒜) (Y := ℬ))) ≫ φ =
    (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ)) ≫ ψ := by
  have h := kernel.condition (biprod.desc φ ψ)
  rw [show kernel.ι (biprod.desc φ ψ) = biprod.lift
    (kernel.ι (biprod.desc φ ψ) ≫ biprod.fst) (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd) from
    by apply biprod.hom_ext <;> simp, biprod.lift_desc] at h
  rw [Preadditive.neg_comp]; exact neg_eq_of_add_eq_zero_right h

set_option linter.unusedSectionVars false in
/-- Vanishing condition needed to factor the cokernel of `pullback.snd` through the
cokernel of `biprod.inl ∘ factorThruImage`. Used in constructing the forward map of the
abstract second isomorphism theorem. -/
lemma secondIso_fwd_cond :
    pullback.snd φ ψ ≫ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫
      cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) = 0 := by
  have h : pullback.fst φ ψ ≫ biprod.inl ≫ factorThruImage (biprod.desc φ ψ) =
    pullback.snd φ ψ ≫ biprod.inr ≫ factorThruImage (biprod.desc φ ψ) := by
    apply (cancel_mono (Limits.image.ι (biprod.desc φ ψ))).mp
    simp only [Category.assoc, image.fac, biprod.inl_desc, biprod.inr_desc]; exact pullback.condition
  have key : (pullback.snd φ ψ ≫ biprod.inr ≫ factorThruImage (biprod.desc φ ψ)) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
    rw [← h]; simp only [Category.assoc, cokernel.condition, comp_zero]
  simp only [Category.assoc] at key ⊢; exact key

set_option linter.unusedSectionVars false in
/-- Vanishing condition: the kernel of `[φ, ψ]` projected to the `ℬ` factor lands in the
image of `pullback.snd`, hence its image in `coker(pullback.snd)` vanishes. -/
lemma secondIso_kernel_kills_snd_cokernel :
    kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) ≫
    cokernel.π (pullback.snd (f := φ) (g := ψ)) = 0 := by
  rw [reassoc_of% (show kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) =
    (pullback.lift (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst))
      (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd)
      (secondIso_kernel_pullback_cond φ ψ)) ≫ pullback.snd φ ψ from by simp [pullback.lift_snd]),
    cokernel.condition, comp_zero]

/-- The induced map `coim([φ, ψ]) → coker(pullback.snd)` from the coimage of the biproduct
map to the cokernel of the pullback projection. -/
def secondIso_coimToCokerPS :
    Abelian.coimage (biprod.desc φ ψ) ⟶ cokernel (pullback.snd (f := φ) (g := ψ)) :=
  cokernel.desc _ (biprod.snd ≫ cokernel.π (pullback.snd (f := φ) (g := ψ)))
    (secondIso_kernel_kills_snd_cokernel φ ψ)

/-- The induced map `image([φ, ψ]) → coker(pullback.snd)`, obtained from
`secondIso_coimToCokerPS` via the canonical iso `image ≅ coimage` in an abelian category. -/
def secondIso_imgToCokerPS :
    Limits.image (biprod.desc φ ψ) ⟶ cokernel (pullback.snd (f := φ) (g := ψ)) :=
  (Abelian.coimageIsoImage' (biprod.desc φ ψ)).inv ≫ secondIso_coimToCokerPS φ ψ

/-- Vanishing condition needed to descend `secondIso_imgToCokerPS` to a map out of the
cokernel `coker(biprod.inl ∘ factorThruImage)`. -/
lemma secondIso_inv_kills_inclA :
    (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ≫ secondIso_imgToCokerPS φ ψ = 0 := by
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc, biprod.inl_snd_assoc, zero_comp]

/-- Forward direction of the abstract second isomorphism: a map from `coker(pullback.snd)`
to `coker(biprod.inl ∘ factorThruImage)`, induced by the inclusion of `ℬ` into the
biproduct. -/
def secondIso_fwd :
    cokernel (pullback.snd (f := φ) (g := ψ)) ⟶
    cokernel (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) :=
  cokernel.desc _ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) (secondIso_fwd_cond φ ψ)

/-- Inverse direction of the abstract second isomorphism: the descent of
`secondIso_imgToCokerPS` from the image to `coker(biprod.inl ∘ factorThruImage)`. -/
def secondIso_inv :
    cokernel (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ⟶
    cokernel (pullback.snd (f := φ) (g := ψ)) :=
  cokernel.desc _ (secondIso_imgToCokerPS φ ψ) (secondIso_inv_kills_inclA φ ψ)

set_option linter.unusedSectionVars false in
/-- The composition `secondIso_fwd ≫ secondIso_inv` is the identity. One half of the
isomorphism claim. -/
lemma secondIso_fwd_inv_id :
    secondIso_fwd φ ψ ≫ secondIso_inv φ ψ = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (pullback.snd (f := φ) (g := ψ)))).mp
  simp only [secondIso_fwd, secondIso_inv, cokernel.π_desc_assoc, Category.comp_id]
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc]
  simp

set_option linter.unusedSectionVars false in
/-- The composition `secondIso_inv ≫ secondIso_fwd` is the identity. The other half of the
isomorphism claim. -/
lemma secondIso_inv_fwd_id :
    secondIso_inv φ ψ ≫ secondIso_fwd φ ψ = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)))).mp
  simp only [secondIso_inv, secondIso_fwd, cokernel.π_desc_assoc, Category.comp_id]
  apply (cancel_epi (factorThruImage (biprod.desc φ ψ))).mp
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc_assoc, cokernel.π_desc]


  have h_fst_zero : biprod.fst (X := 𝒜) (Y := ℬ) ≫ biprod.inl ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
    have h : biprod.inl (X := 𝒜) (Y := ℬ) ≫ factorThruImage (biprod.desc φ ψ) ≫
      cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
      rw [← Category.assoc]; exact cokernel.condition _
    simp only [h, comp_zero]
  have h_total := congr_arg (· ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) (biprod.total (X := 𝒜) (Y := ℬ))
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h_total
  rw [h_fst_zero, zero_add] at h_total
  exact h_total

/-- **Abstract second isomorphism theorem.** *For morphisms `φ : 𝒜 → 𝒳` and `ψ : ℬ → 𝒳` in
an abelian category, there is a canonical isomorphism*
$$(\mathcal{A} + \mathcal{B}) / \mathcal{A} \;\cong\; \mathcal{B} / (\mathcal{A} \cap \mathcal{B}),$$
*where `𝒜 + ℬ` is the image of `[φ, ψ] : 𝒜 ⊕ ℬ → 𝒳` and `𝒜 ∩ ℬ` is the pullback of `φ`
along `ψ`.* -/
def secondIsoOfMorphisms :
    cokernel (biprod.inl (X := 𝒜) (Y := ℬ) ≫ factorThruImage (biprod.desc φ ψ)) ≅
    cokernel (pullback.snd (f := φ) (g := ψ)) where
  hom := secondIso_inv φ ψ
  inv := secondIso_fwd φ ψ
  hom_inv_id := secondIso_inv_fwd_id φ ψ
  inv_hom_id := secondIso_fwd_inv_id φ ψ

end SecondIsoAbstract


/-- The concrete forward map for the second isomorphism applied to chain complexes:
`C^{\{A, B\}}_*(X) → C_*(B, A ∩ B)`. -/
end

end Excision

/-- **Theorem 10.2 (Excision).** *Let `(X, A, U)` be an excisive triple, meaning
`closure U ⊆ interior A`. Then for every `n`, the pair inclusion*
$$(X \setminus U,\; A \setminus U) \hookrightarrow (X, A)$$
*induces an isomorphism on relative singular homology*
$$H_n(X \setminus U,\; A \setminus U;\, \mathbb{Z}) \;\xrightarrow{\sim}\; H_n(X, A;\, \mathbb{Z}).$$

Proved by passing to small chains via the locality principle and the second isomorphism. -/
namespace SphereHomology

/-- The `n`-sphere `S^n = \{x \in \mathbb{R}^{n+1} : \|x\| = 1\}`. -/
def Sphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The subspace topology on `Sphere n`. -/
instance Sphere.instTopologicalSpace (n : ℕ) : TopologicalSpace (Sphere n) :=
  instTopologicalSpaceSubtype

/-- The closed `n`-disk `D^n = \{x \in \mathbb{R}^n : \|x\| \le 1\}`. -/
def Disk (n : ℕ) : Type :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The subspace topology on `Disk n`. -/
instance Disk.instTopologicalSpace (n : ℕ) : TopologicalSpace (Disk n) :=
  instTopologicalSpaceSubtype

/-- The boundary `∂D^n = S^{n-1}` of the `n`-disk, as a stand-alone type. -/
def DiskBoundary (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The boundary `∂D^n ⊆ D^n` as a subset of the `n`-disk. -/
def diskBoundarySubset (n : ℕ) : Set (Disk n) :=
  {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1}

open AlgebraicTopology

noncomputable section


/-- Local copy of `singularChainZ` in the `SphereHomology` namespace: the integer singular
chain complex functor `X ↦ C_*(X; ℤ)`. -/
abbrev singularChainZF : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)


/-- Local copy of `sigmaConst_map_mono_of_injective` in the `SphereHomology` namespace. -/
lemma sigmaConst_map_mono_of_injective'
    (J K : Type) (f : J → K) (hf : Function.Injective f) (R : AddCommGrpCat) :
    Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
  by_cases hJ : Nonempty J
  · exact (⟨Function.invFun f, Function.invFun_comp hf⟩ :
      SplitMono (show J ⟶ K from f)).map (sigmaConst.obj R) |>.mono
  · rw [not_nonempty_iff] at hJ
    exact (show IsZero ((sigmaConst.obj R).obj J) by
      rw [IsZero.iff_id_eq_zero]; apply Sigma.hom_ext
      intro j; exact (hJ.false j).elim).mono _

/-- Local copy of `toSSet_preservesMono` in the `SphereHomology` namespace. -/
instance toSSet_preservesMono' : TopCat.toSSet.{0}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    intro n; rw [mono_iff_injective]
    intro σ₁ σ₂ h
    simp only [TopCat.toSSet, Presheaf.restrictedULiftYoneda, Functor.comp_map,
      Functor.whiskeringLeft, uliftYoneda] at h
    dsimp [Functor.whiskerLeft, yoneda, uliftFunctor] at h
    have h' : σ₁.down ≫ f = σ₂.down ≫ f := by
      have := congr_arg ULift.down h; simp at this; exact this
    exact ULift.ext _ _ ((cancel_mono f).mp h')

/-- The `singularChainZF` functor preserves monomorphisms. -/
instance singularChainZ_preserves_mono : singularChainZF.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))))
    apply sigmaConst_map_mono_of_injective'
    haveI : Mono (TopCat.toSSet.map f) := Functor.map_mono TopCat.toSSet f
    have hmono_app : Mono ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))) :=
      (NatTrans.mono_iff_mono_app (TopCat.toSSet.map f)).mp this _
    exact (mono_iff_injective _).mp hmono_app


/-- The chain-level inclusion `C_*(A) → C_*(X)` for a subspace `A ⊆ X` (local copy of
`subspaceChainInclusion` in the `SphereHomology` namespace). -/
def inclChain (X : Type) [TopologicalSpace X] (A : Set X) :
    singularChainZF.obj (TopCat.of A) ⟶ singularChainZF.obj (TopCat.of X) :=
  singularChainZF.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)


/-- The topological inclusion `A ↪ X` is a monomorphism in `TopCat`. -/
instance inclTopMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.ofHom (⟨(Subtype.val : A → X), continuous_subtype_val⟩ : C(A, X))) := by
  rw [TopCat.mono_iff_injective]; exact Subtype.val_injective


/-- The chain-level inclusion `inclChain` is a monomorphism. -/
instance inclChainMono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (inclChain X A) := by
  haveI := singularChainZ_preserves_mono
  exact Functor.PreservesMonomorphisms.preserves _


/-- The pair short exact sequence `0 → C_*(A) → C_*(X) → C_*(X)/C_*(A) → 0`. -/
def pairSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (inclChain X A) (cokernel.π (inclChain X A)) (cokernel.condition _)

/-- The left map of the pair short exact sequence is a monomorphism. -/
instance pairSES_f_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (pairSES X A).f := inclChainMono X A

/-- The right map of the pair short exact sequence is an epimorphism. -/
instance pairSES_g_epi (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (pairSES X A).g := by
  change Epi (cokernel.π (inclChain X A))
  infer_instance

/-- The pair sequence is short exact. -/
def pairSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (pairSES X A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)


/-- The boundary-map isomorphism in the pair long exact sequence under vanishing of the
homology of `C_*(X)` in two adjacent degrees: `H_{q+1}(X, A) ≅ H_q(A)`. -/
noncomputable def pairδIso (X : Type) [TopologicalSpace X] (A : Set X)
    (q : ℕ)
    (hi : IsZero ((pairSES X A).X₂.homology (q + 1)))
    (hj : IsZero ((pairSES X A).X₂.homology q)) :
    (pairSES X A).X₃.homology (q + 1) ≅ (pairSES X A).X₁.homology q :=
  (pairSES_shortExact X A).δIso (q + 1) q (by rw [ComplexShape.down_Rel]) hi hj


/-- The natural identification `∂D^{n+2} ≅ S^{n+1}` between the boundary subspace and the
sphere of the appropriate dimension, as objects of `TopCat`. -/
noncomputable def bdryToSphereIso (n : ℕ) :
    TopCat.of ↥(diskBoundarySubset (n + 2)) ≅ TopCat.of (Sphere (n + 1)) where
  hom := TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hsp⟩ => ⟨x, hsp⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩
  inv := TopCat.ofHom ⟨fun ⟨x, hsp⟩ => ⟨⟨x, Metric.sphere_subset_closedBall hsp⟩, hsp⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _⟩
  hom_inv_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨⟨_, _⟩, _⟩; rfl
  inv_hom_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨_, _⟩; rfl

end


/-- Auxiliary form of `sphere_homology_top`: the top homology of `S^n` is `ℤ`, expressed in
terms of the `singularChainZF` complex. -/
noncomputable instance suspSingularChainZ_preserves_mono :
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ) :
      TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ).PreservesMonomorphisms :=
  singularChainZ_preserves_mono

section SuspensionIsoProof

open AlgebraicTopology

noncomputable section


/-- Local copy of `singularChainZF` in the suspension-isomorphism proof. -/
abbrev suspSingularChainZF : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- Local copy of `inclChain` for the suspension-isomorphism proof. -/
noncomputable def suspInclChain (X : Type) [TopologicalSpace X] (A : Set X) :
    suspSingularChainZF.obj (TopCat.of A) ⟶ suspSingularChainZF.obj (TopCat.of X) :=
  suspSingularChainZF.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

/-- Local copy of `inclTopMono` for the suspension-isomorphism proof. -/
instance suspInclTopMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.ofHom (⟨(Subtype.val : A → X), continuous_subtype_val⟩ : C(A, X))) := by
  rw [TopCat.mono_iff_injective]; exact Subtype.val_injective

/-- Local copy of `inclChainMono` for the suspension-isomorphism proof. -/
instance suspInclChainMono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (suspInclChain X A) := by
  haveI := suspSingularChainZ_preserves_mono
  exact Functor.PreservesMonomorphisms.preserves _

/-- Local copy of `pairSES` for the suspension-isomorphism proof. -/
def suspPairSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (suspInclChain X A) (cokernel.π (suspInclChain X A)) (cokernel.condition _)

/-- Local copy of `pairSES_f_mono` for the suspension-isomorphism proof. -/
instance suspPairSES_f_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (suspPairSES X A).f := suspInclChainMono X A

/-- Local copy of `pairSES_g_epi` for the suspension-isomorphism proof. -/
instance suspPairSES_g_epi (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (suspPairSES X A).g := by
  change Epi (cokernel.π (suspInclChain X A))
  infer_instance

/-- Local copy of `pairSES_shortExact` for the suspension-isomorphism proof. -/
def suspPairSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (suspPairSES X A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- Local copy of `pairδIso` for the suspension-isomorphism proof. -/
noncomputable def suspPairδIso (X : Type) [TopologicalSpace X] (A : Set X)
    (q : ℕ)
    (hi : IsZero ((suspPairSES X A).X₂.homology (q + 1)))
    (hj : IsZero ((suspPairSES X A).X₂.homology q)) :
    (suspPairSES X A).X₃.homology (q + 1) ≅ (suspPairSES X A).X₁.homology q :=
  (suspPairSES_shortExact X A).δIso (q + 1) q (by rw [ComplexShape.down_Rel]) hi hj


/-- Local copy of `bdryToSphereIso`: the identification `∂D^{n+1} ≅ S^n`. -/
noncomputable def suspBdryToSphereIso (n : ℕ) :
    TopCat.of ↥(diskBoundarySubset (n + 1)) ≅ TopCat.of (Sphere n) where
  hom := TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hsp⟩ => ⟨x, hsp⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩
  inv := TopCat.ofHom ⟨fun ⟨x, hsp⟩ => ⟨⟨x, Metric.sphere_subset_closedBall hsp⟩, hsp⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _⟩
  hom_inv_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨⟨_, _⟩, _⟩; rfl
  inv_hom_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨_, _⟩; rfl

end

/-- **Suspension isomorphism for sphere homology.** For `q ≥ 1`, there is an isomorphism
`H_q(S^n) ≅ H_{q+1}(S^{n+1})`, obtained by chasing the pair long exact sequences of
`(D^{n+1}, S^n)` and `(D^{n+2}, S^{n+1})` together with the known relative homology of
the disk pair. -/
end SuspensionIsoProof

/-- `S^0` is finite (it is just the two-point set `{-1, +1}`). -/
instance sphere_zero_finite : Empty.Finite (Sphere 0) := by
  show Empty.Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
  rw [Set.finite_coe_iff]
  let p1 : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ))
  let p2 : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ))
  apply Set.Finite.subset (Set.Finite.insert p1 (Set.finite_singleton p2))
  intro x hx
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hn := EuclideanSpace.norm_eq x
  rw [hx] at hn
  simp only [Fin.sum_univ_one] at hn
  rw [Real.sqrt_sq (norm_nonneg _)] at hn
  have habsx : x.ofLp 0 = 1 ∨ x.ofLp 0 = -1 := by
    rw [Real.norm_eq_abs] at hn
    exact abs_eq (by norm_num : (1 : ℝ) ≥ 0) |>.mp hn.symm
  rcases habsx with h | h
  · left; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p1]
  · right; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p2]

/-- `S^0` is totally disconnected (discrete two-point space). -/
instance sphere_zero_totallyDisconnected : TotallyDisconnectedSpace (Sphere 0) := by
  haveI : T1Space (Sphere 0) := by
    show T1Space ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    infer_instance
  haveI : DiscreteTopology (Sphere 0) := Finite.instDiscreteTopology
  infer_instance

/-- **Proposition 10.4 (packaged).** The singular homology of spheres and the relative
homology of disk pairs: `H_n(S^n) = ℤ`, `H_0(S^n) = ℤ` for `n > 0`,
`H_0(S^0) = ℤ ⊕ ℤ`, otherwise zero; and `H_n(D^n, S^{n-1}) = ℤ`, otherwise zero. -/
structure SphereAndDiskHomology : Prop where
  sphere_top : ∀ (n : ℕ), n > 0 →
    Nonempty (SingularHomologyGroup n (Sphere n) ≅ AddCommGrpCat.of ℤ)
  sphere_zero : ∀ (n : ℕ), n > 0 →
    Nonempty (SingularHomologyGroup 0 (Sphere n) ≅ AddCommGrpCat.of ℤ)
  sphere_zero_zero :
    Nonempty (SingularHomologyGroup 0 (Sphere 0) ≅ AddCommGrpCat.of (ℤ × ℤ))
  sphere_vanishing : ∀ (q n : ℕ), n > 0 → q ≠ 0 → q ≠ n →
    IsZero (SingularHomologyGroup q (Sphere n))
  sphere_zero_vanishing : ∀ (q : ℕ), q > 0 →
    IsZero (SingularHomologyGroup q (Sphere 0))
  relative_top : ∀ (n : ℕ), n > 0 →
    Nonempty (Excision.RelativeSingularHomologyGroup n (Disk n) (diskBoundarySubset n) ≅
      AddCommGrpCat.of ℤ)
  relative_vanishing : ∀ (q n : ℕ), n > 0 → q ≠ n →
    IsZero (Excision.RelativeSingularHomologyGroup q (Disk n) (diskBoundarySubset n))


open AlgebraicTopology

section SuspensionVanishing

noncomputable section

/-- **Top homology of the sphere.** `H_n(S^n) ≅ ℤ` for `n > 0`. -/
end

/-- Inductive step for sphere-homology vanishing: if `H_q(S^n) = 0` for `q ≥ 1`, then
`H_{q+1}(S^{n+1}) = 0`. -/
end SuspensionVanishing

/-- **Off-degree vanishing of sphere homology.** For `n > 0`, `0 < q ≠ n`, we have
`H_q(S^n) = 0`. The proof is a two-variable induction on `q + n`, combining
`sphere_h1_vanishing`, `sphere_zero_homology_vanishing`, and `suspension_vanishing_step`. -/
noncomputable def homotopyEquiv_singularHomologyIso {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (q : ℕ) :
    SingularHomologyGroup q X ≅ SingularHomologyGroup q Y := by
  open AlgebraicTopology CategoryTheory in

  let F := ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ))
  let fwd : (TopCat.of X) ⟶ (TopCat.of Y) := TopCat.ofHom e.toFun
  let bwd : (TopCat.of Y) ⟶ (TopCat.of X) := TopCat.ofHom e.invFun


  let Hl := e.left_inv.some
  let Hr := e.right_inv.some
  change F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y)

  have hfwd_bwd : F.map (fwd ≫ bwd) = F.map (𝟙 _) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (show TopCat.Homotopy (fwd ≫ bwd) (𝟙 _) from Hl)
      (AddCommGrpCat.of ℤ) q
  have hbwd_fwd : F.map (bwd ≫ fwd) = F.map (𝟙 _) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (show TopCat.Homotopy (bwd ≫ fwd) (𝟙 _) from Hr)
      (AddCommGrpCat.of ℤ) q
  have h1 : F.map fwd ≫ F.map bwd = 𝟙 _ := by
    rw [← F.map_comp, hfwd_bwd, F.map_id]
  have h2 : F.map bwd ≫ F.map fwd = 𝟙 _ := by
    rw [← F.map_comp, hbwd_fwd, F.map_id]
  exact ⟨F.map fwd, F.map bwd, h1, h2⟩

/-- A homeomorphism `f : X ≃ₜ Y` restricts to a homeomorphism
`{x | x ≠ p} ≃ₜ {y | y ≠ f p}` between punctured spaces. -/
def homeomorphSubtypeNe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) :
    {y : X | y ≠ x} ≃ₜ {z : Y | z ≠ f x} where
  toEquiv := f.toEquiv.subtypeEquiv fun _ =>
    ⟨fun h => f.injective.ne h, fun h e => h (congrArg f e)⟩
  continuous_toFun :=
    Continuous.subtype_mk ((map_continuous f).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk ((map_continuous f.symm).comp continuous_subtype_val) _

/-- Translation by `-p` gives a homeomorphism `{x | x ≠ p} ≃ₜ {y | y ≠ 0}`. -/
def puncturedTranslateHomeomorph {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (p : G) :
    {x : G | x ≠ p} ≃ₜ {y : G | y ≠ 0} := by
  refine (homeomorphSubtypeNe (Homeomorph.addRight (-p)) p).trans
    (Homeomorph.ofEqSubtypes ?_)
  ext x
  simp [add_neg_cancel]

/-- **Corollary 10.6 (Invariance of dimension).** If `m ≠ n`, then `ℝ^m` and `ℝ^n` are not
homeomorphic. The proof punctures the spaces, applies the homotopy equivalence
`ℝ^{n+1} ∖ {0} ≃ₕ S^n`, and uses that spheres of different dimensions are not
homotopy equivalent. -/
end SphereHomology

namespace BrouwerFixedPoint

open Metric Set Inner

/-- Local abbreviation for the closed unit disk `D^n ⊆ ℝ^n` in the Brouwer fixed-point
section. -/
abbrev Disk (n : ℕ) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Local abbreviation for the unit sphere `S^{n-1} ⊆ ℝ^n` in the Brouwer fixed-point
section. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- A *retraction* of `D^n` onto `S^{n-1}`: a continuous map `r : ℝ^n → ℝ^n` sending the
disk to the sphere and fixing the boundary. Brouwer's theorem amounts to ruling out such
retractions. -/
structure IsRetraction (n : ℕ) (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  continuous_r : Continuous r
  maps_to : ∀ x, x ∈ Disk n → r x ∈ Sphere n
  fixes_boundary : ∀ x, x ∈ Sphere n → r x = x


/-- The functor `H_k(−; ℤ) : TopCat → AddCommGrpCat`, packaged for use in the Brouwer proof. -/
noncomputable abbrev homFunctorZ (k : ℕ) : TopCat.{0} ⥤ AddCommGrpCat :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)


/-- The inclusion `S^{n-1} ↪ D^n` of the boundary sphere into the disk, as a morphism of
`TopCat`. -/
noncomputable def sphereInclusion (n : ℕ) :
    TopCat.of ↥(Sphere n) ⟶ TopCat.of ↥(Disk n) :=
  TopCat.ofHom ⟨Set.inclusion Metric.sphere_subset_closedBall,
    continuous_inclusion _⟩


/-- A retraction `r : ℝ^n → ℝ^n` of `D^n` onto `S^{n-1}` packaged as a `TopCat` morphism
`D^n ⟶ S^{n-1}`. -/
noncomputable def diskRetraction (n : ℕ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : IsRetraction n r) :
    TopCat.of ↥(Disk n) ⟶ TopCat.of ↥(Sphere n) :=
  TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨r x, hr.maps_to x hx⟩,
    Continuous.subtype_mk (hr.continuous_r.comp continuous_subtype_val) _⟩


/-- The projection `ℝ^1 → ℝ` onto the (only) coordinate, as a continuous linear map. -/
noncomputable def coordProj : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)


/-- **No retraction `D^{m+1} → S^m`** for `m ≥ 1` (inductive step for Brouwer). If such a
retraction existed, then `H_m(S^m) ≅ ℤ` would be a retract of `H_m(D^{m+1}) = 0`,
contradiction. -/
noncomputable def rayDiscrim {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2)

/-- The positive root `t = (−⟨a,v⟩ + √Δ) / ‖v‖²` of the equation `‖a + t v‖ = 1`, where
`Δ = rayDiscrim a v`. Geometrically: the parameter at which the ray `t ↦ a + t v`
(with `t ≥ 0`) hits the unit sphere. -/
noncomputable def rayParam {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (-inner (𝕜 := ℝ) a v + Real.sqrt (rayDiscrim a v)) / ‖v‖ ^ 2

/-- Geometric retraction associated to a fixed-point-free self-map `f` of `D^n`: from each
point `x`, follow the ray from `f x` through `x` until it hits the boundary sphere. -/
noncomputable def retractionMap {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  f x + rayParam (f x) (x - f x) • (x - f x)

/-- Radial projection of `ℝ^n` onto the closed unit ball: `x ↦ x / max(1, ‖x‖)`. -/
noncomputable def projBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (max 1 ‖x‖)⁻¹ • x

/-- A subset `A ⊆ B` is a *deformation retract within `B`* if `A ⊆ B` and there exists a
deformation retraction of `B` onto `A` (viewed as a subset of `B`). Hypothesis of
Corollary 10.3. -/
def IsSubspaceDeformationRetract {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  A ⊆ B ∧ Nonempty (DeformationRetract.IsDeformationRetract (Subtype.val ⁻¹' A : Set ↥B))

/-- The equivalence relation on `X` that collapses the subset `A` to a single point: two points
are related iff they are equal, or both lie in `A`. Used to form the quotient `X / A`. -/
def collapseSetoid {X : Type u} [TopologicalSpace X] (A : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun heq => Or.inl heq.symm) (fun ⟨hx, hy⟩ => Or.inr ⟨hy, hx⟩)
    trans := fun h1 h2 => by
      rcases h1 with rfl | ⟨hx, _⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, hz⟩ <;> exact Or.inr ⟨hx, ‹_›⟩
  }

/-- The quotient space `X / A`: the set of equivalence classes of `collapseSetoid A`, with the
quotient topology. -/
def QuotientSpace (X : Type u) [TopologicalSpace X] (A : Set X) :=
  Quotient (collapseSetoid A)

/-- The quotient topology on `QuotientSpace X A`. -/
instance {X : Type u} [TopologicalSpace X] (A : Set X) :
    TopologicalSpace (QuotientSpace X A) :=
  instTopologicalSpaceQuotient

/-- The basepoint of `X / A`: the image in `QuotientSpace X A` of any point `a ∈ A`. -/
def quotientBasepoint {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (_ : a ∈ A) : QuotientSpace X A :=
  Quotient.mk (collapseSetoid A) a

/-- The pointed pair `(X / A, [a])` where `[a]` is the collapsed image of `A`. -/
def quotientPair {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (ha : a ∈ A) : TopPair where
  space := QuotientSpace X A
  instTop := inferInstance
  sub := {quotientBasepoint A ha}

/-- The quotient map of pairs `(X, A) → (X/A, *)` sending each point to its equivalence class. -/
def collapseMapOfPairs {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (ha : a ∈ A) :
    MapOfPairs ⟨X, inferInstance, A⟩ (quotientPair A ha) where
  toFun := Quotient.mk (collapseSetoid A)
  continuous_toFun := continuous_quotient_mk'
  mapsTo := fun _ hx => Quotient.sound (Or.inr ⟨hx, ha⟩)

/-- The pair `(B, A ∩ B)` viewed inside `B` via the subtype inclusion `↥B ↪ X`. -/
def subspacePair {X : Type u} [TopologicalSpace X] (A B : Set X) : TopPair where
  space := ↥B
  instTop := inferInstance
  sub := Subtype.val ⁻¹' A

/-- The pair map `(B, A ∩ B) → (X, A)` given by the subtype inclusion `↥B ↪ X`. -/
def pairInclusion {X : Type u} [TopologicalSpace X] (A B : Set X) :
    MapOfPairs (subspacePair A B) ⟨X, inferInstance, A⟩ where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ hx => hx

variable {X : Type u} [TopologicalSpace X]

/-- Identification of `(B, A ∩ B)` with the excised pair `(X ∖ Bᶜ, A ∖ Bᶜ)` in the forward
direction. -/
def subspacePairToExcisePair (A B : Set X) :
    MapOfPairs (subspacePair A B)
      ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [compl_compl]; exact hx⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun ⟨_, _⟩ hxA => hxA

/-- Identification of the excised pair `(X ∖ Bᶜ, A ∖ Bᶜ)` with `(B, A ∩ B)` in the reverse
direction. Inverse to `subspacePairToExcisePair`. -/
def excisePairToSubspacePair (A B : Set X) :
    MapOfPairs ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ)
      (subspacePair A B) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rwa [compl_compl] at hx⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun ⟨_, _⟩ hxA => hxA

/-- The homology map `H_n(B, A ∩ B) → H_n(X/A, *)` induced by the composition
"include into `(X, A)` then collapse `A`". This is the factorization used to deduce
that the collapse map induces an isomorphism on homology (Corollary 10.3). -/
def collapseFactorization
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    {a : X} (ha : a ∈ A)
    (_hClosure : closure A ⊆ interior B) (_hDR : IsSubspaceDeformationRetract A B) :
    h.H n (subspacePair A B) →+ h.H n (quotientPair A ha) :=
  h.map n ((collapseMapOfPairs A ha).comp (pairInclusion A B))

/-- The functor `Top ⥤ AddCommGrp` sending a space `X` to its `n`-th singular homology group
$H_n(X; \mathbb{Z})$ with integer coefficients. -/
abbrev homologyFunctorZ (n : ℕ) : TopCat.{0} ⥤ AddCommGrpCat :=
  (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)

/-- Any endomorphism `f : ℤ ⟶ ℤ` in `AddCommGrp` is multiplication by `f 1`. -/
lemma addCommGrpCat_endZ_apply
    (f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (x : ℤ) :
    f x = f 1 * x := by
  change (ConcreteCategory.hom f) x = (ConcreteCategory.hom f) 1 * x
  have h := (ConcreteCategory.hom f).map_zsmul 1 x
  simp only [smul_eq_mul, mul_one] at h
  rw [h, mul_comm]

/-- The *degree* of an endomorphism `e : G ⟶ G` of an abelian group `G ≅ ℤ`: transport `e`
along the chosen isomorphism `φ : G ≅ ℤ` and evaluate at `1`. -/
def degreeOfEndo {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ)
    (e : G ⟶ G) : ℤ :=
  (φ.inv ≫ e ≫ φ.hom) (1 : ℤ)

/-- Multiplicativity of degree: `deg(e₁ ∘ e₂) = deg(e₁) · deg(e₂)`. -/
lemma degreeOfEndo_comp {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ)
    (e₁ e₂ : G ⟶ G) :
    degreeOfEndo φ (e₁ ≫ e₂) = degreeOfEndo φ e₁ * degreeOfEndo φ e₂ := by
  simp only [degreeOfEndo]
  have hfact : (φ.inv ≫ (e₁ ≫ e₂) ≫ φ.hom : AddCommGrpCat.of ℤ ⟶ _) =
      (φ.inv ≫ e₁ ≫ φ.hom) ≫ (φ.inv ≫ e₂ ≫ φ.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h1 : ((φ.inv ≫ (e₁ ≫ e₂) ≫ φ.hom : AddCommGrpCat.of ℤ ⟶ _) (1 : ℤ)) =
      ((φ.inv ≫ e₂ ≫ φ.hom) ((φ.inv ≫ e₁ ≫ φ.hom) (1 : ℤ))) := by
    rw [hfact]; rfl
  rw [h1, addCommGrpCat_endZ_apply (φ.inv ≫ e₂ ≫ φ.hom)]
  ring

/-- The degree of the identity endomorphism is `1`. -/
lemma degreeOfEndo_id {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ) :
    degreeOfEndo φ (𝟙 G) = 1 := by
  simp only [degreeOfEndo, Category.id_comp, Iso.inv_hom_id]; rfl

/-- The homotopy equivalence relation on self-maps of `S`: two continuous maps `f, g : S → S`
are related iff there is a homotopy from `f` to `g`. -/
def selfMapSetoid (S : TopCat.{0}) : Setoid (S ⟶ S) where
  r f g := Nonempty (TopCat.Homotopy f g)
  iseqv := {
    refl := fun _ => ⟨ContinuousMap.Homotopy.refl _⟩
    symm := fun ⟨H⟩ => ⟨H.symm⟩
    trans := fun ⟨H₁⟩ ⟨H₂⟩ => ⟨H₁.trans H₂⟩
  }

/-- Homotopy classes of self-maps of `S`, denoted `[S, S]`. -/
def SelfMapHomotopyClass (S : TopCat.{0}) := Quotient (selfMapSetoid S)

/-- The monoid structure on `[S, S]` induced by composition of representatives. -/
instance (S : TopCat.{0}) : Monoid (SelfMapHomotopyClass S) where
  mul := Quotient.lift₂ (fun f g => @Quotient.mk _ (selfMapSetoid S) (f ≫ g))
    (fun _ _ _ _ hf hg => Quotient.sound (ContinuousMap.Homotopic.comp hg hf))
  one := @Quotient.mk _ (selfMapSetoid S) (𝟙 S)
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.assoc]; exact ⟨ContinuousMap.Homotopy.refl _⟩
  one_mul := by
    intro a; induction a using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.id_comp]; exact ⟨ContinuousMap.Homotopy.refl _⟩
  mul_one := by
    intro a; induction a using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.comp_id]; exact ⟨ContinuousMap.Homotopy.refl _⟩

/-- The *degree homomorphism* `deg : [S, S] → ℤ` for a space `S` with `H_n(S) ≅ ℤ`: assigns
to each homotopy class of self-maps `[f]` the degree of the induced endomorphism of
`H_n(S)`. Multiplicative under composition. -/
def degreeHom (n : ℕ) (S : TopCat.{0})
    (φ : (homologyFunctorZ n).obj S ≅ AddCommGrpCat.of ℤ) :
    SelfMapHomotopyClass S →* ℤ where
  toFun := Quotient.lift (fun f => degreeOfEndo φ ((homologyFunctorZ n).map f))
    (fun _ _ ⟨H⟩ => by
      show degreeOfEndo φ _ = degreeOfEndo φ _
      congr 1
      exact H.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n)
  map_one' := by
    show degreeOfEndo φ ((homologyFunctorZ n).map (𝟙 S)) = 1
    rw [(homologyFunctorZ n).map_id S]; exact degreeOfEndo_id φ
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    show degreeOfEndo φ ((homologyFunctorZ n).map (_ ≫ _)) = _
    rw [(homologyFunctorZ n).map_comp]
    exact degreeOfEndo_comp φ _ _

/-- The `n`-sphere `S^n ⊆ ℝ^{n+1}` packaged as an object of `TopCat`. -/
def sphereTopCat (n : ℕ) : TopCat.{0} :=
  TopCat.of (SphereHomology.Sphere n)


/-- Safe normalization map `ℝ^{n+1} → S^n`: sends a non-zero vector `w` to `w / ‖w‖` and
maps `0` to the basepoint `e_0`, so as to be defined everywhere. -/
noncomputable def suspSafeNorm (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    SphereHomology.Sphere n :=
  if hw : w = 0 then ⟨EuclideanSpace.single 0 1, by simp [mem_sphere_iff_norm]⟩
  else ⟨‖w‖⁻¹ • w, by
    simp [mem_sphere_iff_norm, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩

/-- Project an element of `ℝ^{n+2}` onto its first `n+1` coordinates, viewed as an element
of `ℝ^{n+1}`. -/
noncomputable def suspInitProj (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv _ _).symm (fun i => v (Fin.castSucc i))

/-- Append a real scalar `t` as the last coordinate to a vector in `ℝ^{n+1}`, producing a
vector in `ℝ^{n+2}`. -/
noncomputable def suspSnocProj (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv _ _).symm (Fin.snoc (EuclideanSpace.equiv _ _ w) t)

/-- The *raw suspension* of a self-map `f : S^n → S^n`: a map `ℝ^{n+2} → ℝ^{n+2}` that scales
the first `n+1` coordinates by `f` (after radial normalization) and leaves the last
coordinate unchanged. Restricted to `S^{n+1}` this defines the topological suspension. -/
noncomputable def suspRaw (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n)
    (v : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  suspSnocProj n
    (‖suspInitProj n v‖ • (f.1 (suspSafeNorm n (suspInitProj n v))).val)
    (v (Fin.last (n + 1)))

/-- The raw suspension `suspRaw n f` preserves the unit sphere: if `‖v‖ = 1` then
`‖suspRaw n f v‖ = 1`. This is what makes `suspRaw` descend to a well-defined map
`S^{n+1} → S^{n+1}`. -/
lemma suspRaw_norm (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n)
    (v : EuclideanSpace ℝ (Fin (n + 2))) (hv : ‖v‖ = 1) :
    ‖suspRaw n f v‖ = 1 := by
  have sph_norm_fact : ‖(f.1 (suspSafeNorm n (suspInitProj n v))).val‖ = 1 := by
    have := (f.1 (suspSafeNorm n (suspInitProj n v))).property
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have snoc_norm : ‖suspRaw n f v‖ ^ 2 =
      ‖(‖suspInitProj n v‖ • (f.1 (suspSafeNorm n (suspInitProj n v))).val)‖ ^ 2 +
      (v (Fin.last (n + 1))) ^ 2 := by
    simp [suspRaw, EuclideanSpace.real_norm_sq_eq, suspSnocProj, Fin.sum_univ_castSucc,
          Fin.snoc_castSucc, Fin.snoc_last]
  rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), sph_norm_fact, mul_one] at snoc_norm
  have norm_decomp : 1 = ‖suspInitProj n v‖ ^ 2 + (v (Fin.last (n + 1))) ^ 2 := by
    have := congr_arg (· ^ 2) hv; simp only [one_pow] at this; rw [← this]
    simp [EuclideanSpace.real_norm_sq_eq, suspInitProj, Fin.sum_univ_castSucc]
  nlinarith [norm_nonneg (suspRaw n f v), sq_nonneg (‖suspRaw n f v‖ - 1),
             snoc_norm.trans norm_decomp.symm]

/-- Away from zero, the safe normalization map is given by the expected formula
`w ↦ w / ‖w‖`. -/
lemma suspSafeNorm_val_of_ne_zero (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1)))
    (hw : w ≠ 0) : (suspSafeNorm n w).val = ‖w‖⁻¹ • w := by
  simp [suspSafeNorm, hw]

/-- Continuity of the raw suspension `suspRaw n f`. The only non-trivial point is `w = 0`
in the first `n+1` coordinates, where the radial normalization is squeezed to `0` by the
boundedness `‖f(·)‖ = 1`. -/
lemma continuous_suspRaw (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n) :
    Continuous (suspRaw n f) := by
  unfold suspRaw suspSnocProj
  apply (EuclideanSpace.equiv _ _).symm.continuous.comp
  apply continuous_pi; intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]
    exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last (n + 1))).continuous
  · intro j; simp only [Fin.snoc_castSucc]
    have h_init_cont : Continuous (suspInitProj n) := by
      apply (EuclideanSpace.equiv _ _).symm.continuous.comp
      exact continuous_pi (fun i => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).continuous)
    have h_core : Continuous (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        ‖w‖ • (f.1 (suspSafeNorm n w)).val) := by
      rw [continuous_iff_continuousAt]; intro w; by_cases hw : w = 0
      · subst hw
        change Filter.Tendsto _ (nhds 0)
          (nhds (‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖ • _))
        simp only [norm_zero, zero_smul]
        apply squeeze_zero_norm
          (f := fun x => ‖x‖ • (f.1 (suspSafeNorm n x)).val)
        · intro x
          have : ‖(f.1 (suspSafeNorm n x)).val‖ = 1 := by
            have := (f.1 (suspSafeNorm n x)).property
            rwa [Metric.mem_sphere, dist_zero_right] at this
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), this, mul_one]
        · simpa [norm_zero] using
            continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin (n + 1)))
      · apply ContinuousAt.smul continuous_norm.continuousAt
        have h_sNorm_at : ContinuousAt (suspSafeNorm n) w := by
          have hval : ContinuousAt (fun x => (suspSafeNorm n x).val) w :=
            (ContinuousAt.smul
              (ContinuousAt.inv₀ continuous_norm.continuousAt (norm_ne_zero_iff.mpr hw))
              continuousAt_id).congr
              (Filter.eventually_of_mem (isOpen_ne.mem_nhds hw)
                (fun x hx => (suspSafeNorm_val_of_ne_zero n x hx).symm))
          rw [ContinuousAt] at hval ⊢
          change Filter.Tendsto (suspSafeNorm n) (nhds w)
            (@nhds (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) _ _)
          rw [nhds_subtype]
          exact Filter.tendsto_comap_iff.mpr hval

        exact (continuous_subtype_val.comp f.1.continuous).continuousAt.comp h_sNorm_at
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (h_core.comp h_init_cont))

/-- The (unreduced) **suspension** `Σf : S^{n+1} → S^{n+1}` of a self-map `f : S^n → S^n`,
obtained by restricting `suspRaw n f` to the unit sphere. -/
noncomputable def suspensionOfSphereMap (n : ℕ) (_hn : n ≥ 1)
    (f : sphereTopCat n ⟶ sphereTopCat n) :
    sphereTopCat (n + 1) ⟶ sphereTopCat (n + 1) :=
  ⟨⟨fun v => ⟨suspRaw n f v.val, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact suspRaw_norm n f v.val
        (by have := v.property; rwa [Metric.mem_sphere, dist_zero_right] at this)⟩,
    Continuous.subtype_mk ((continuous_suspRaw n f).comp continuous_subtype_val) _⟩⟩

/-- The homology endomorphism induced by `Σf : S^{n+1} → S^{n+1}` agrees, up to the
suspension isomorphism `α : H_n(S^n) ≅ H_{n+1}(S^{n+1})`, with the endomorphism induced by
`f` on `H_n(S^n)`. -/
lemma update_neg_mem_sphere (n : ℕ) (i : Fin (n + 1))
    (x : SphereHomology.Sphere n) :
    (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  have hx := x.2
  simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
  simp only [EuclideanSpace.norm_eq] at hx ⊢
  rw [show (∑ j : Fin (n + 1), ‖((WithLp.equiv 2 _).symm
    (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i)))).ofLp j‖ ^ 2) =
    (∑ j : Fin (n + 1), ‖x.1.ofLp j‖ ^ 2) from by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst h; simp [Function.update_self, norm_neg]
      · simp [Function.update_of_ne h]]
  exact hx

/-- The coordinate reflection map on `ℝ^{n+1}` (negating the `i`-th coordinate) is
continuous. -/
lemma continuous_update_neg (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun v : EuclideanSpace ℝ (Fin (n + 1)) =>
      (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ v) i (-(v i)))) :=
  (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).symm.continuous.comp
    (Continuous.update (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).continuous i
      (((continuous_apply i).comp
        (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).continuous).neg))

/-- The *antipodal map* `S^n → S^n`, `x ↦ -x`. Has degree `(-1)^{n+1}`. -/
def antipodalMap (n : ℕ) : sphereTopCat n ⟶ sphereTopCat n :=
  ⟨⟨fun x => ⟨-x.1, by
      have hx := x.2
      simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
      rw [norm_neg]; exact hx⟩,
    (continuous_neg.comp continuous_subtype_val).subtype_mk _⟩⟩

/-- The *coordinate reflection* `r_i : S^n → S^n` that negates the `i`-th coordinate and
fixes the others. Has degree `-1`. -/
def coordReflection (n : ℕ) (i : Fin (n + 1)) : sphereTopCat n ⟶ sphereTopCat n :=
  ⟨⟨fun x => ⟨(WithLp.equiv 2 _).symm
      (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))),
      update_neg_mem_sphere n i x⟩,
    (continuous_update_neg n i).comp continuous_subtype_val |>.subtype_mk _⟩⟩

/-- The composition of the first `k` coordinate reflections `r_{k-1} ∘ ... ∘ r_0`, a self-map
of `S^n`. Taking `k = n + 1` recovers the antipodal map (up to homotopy). -/
def iteratedReflection (n : ℕ) :
    (k : ℕ) → (hk : k ≤ n + 1) → (sphereTopCat n ⟶ sphereTopCat n)
  | 0, _ => 𝟙 _
  | k + 1, hk => coordReflection n ⟨k, by omega⟩ ≫ iteratedReflection n k (by omega)


/-- Each coordinate reflection `r_i : S^n → S^n` has degree `-1`. -/
end DegreeTheory
