/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section1
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section10
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Category.Grp.Abelian

namespace CWComplex

variable (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

/-- **Definition 16.1.** The group of cellular `n`-chains of a CW complex `X`, defined as the
free abelian group on the set of `n`-cells of `X`. -/
abbrev cellularChains (n : ℕ) : Type _ :=
  FreeAbelianGroup (cells X n)

/-- The relative singular homology group `H_n(A, B)` for two subsets `A, B ⊆ Y` of a
topological space `Y`. -/
section SkeletonPair

variable [T2Space X]

/-- The previous skeleton `X_{n-1}` for `n ≥ 1`, and the empty set for `n = 0`. Convenient
shorthand used for forming the CW-pair `(X_n, X_{n-1})`. -/
noncomputable def prevSkeleton (n : ℕ) : Set X :=
  match n with
  | 0 => ∅
  | k + 1 => ↑(skeleton X k)

/-- The cellular chain group `C_n(X)` is isomorphic to the relative singular homology
`H_n(X_n, X_{n-1})` of the CW-pair (Definition 16.1 of Miller). -/
end SkeletonPair

end CWComplex

open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI

noncomputable section


namespace CWComplex.SkeletonHomology

variable (X : Type) [TopologicalSpace X] [T2Space X]
variable [Topology.CWComplex (Set.univ : Set X)]

/-- The continuous inclusion of the `k`-skeleton `X_k ↪ X`, viewed as a morphism in `TopCat`. -/
def skeletonInclusion (k : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X k : Set X) ⟶ TopCat.of X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The map on singular homology `H_q(X_k) → H_q(X)` induced by the inclusion of the
`k`-skeleton. -/
def skeletonHomologyMap (q k : ℕ) :
    SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X) ⟶
    SingularHomologyGroup q X :=
  ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
    (skeletonInclusion X k)

/-- The one-step skeleton inclusion `X_k ↪ X_{k+1}`, viewed as a morphism in `TopCat`. -/
def skeletonStepInclusion (k : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X k : Set X) ⟶
    TopCat.of ↥(CWComplex.skeleton X (k + 1) : Set X) :=
  ⟨Set.inclusion (Topology.RelCWComplex.skeleton_mono (by norm_cast; omega)),
   continuous_inclusion _⟩

/-- The map on singular homology `H_q(X_k) → H_q(X_{k+1})` induced by the one-step
skeleton inclusion. -/
def skeletonStepHomologyMap (q k : ℕ) :
    SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X) ⟶
    SingularHomologyGroup q ↥(CWComplex.skeleton X (k + 1) : Set X) :=
  ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
    (skeletonStepInclusion X k)

/-- The preimage of `X_m` under the inclusion `X_{m+1} ↪ X` is homeomorphic to `X_m`. -/
def skeletonPreimageHomeo
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m : ℕ) :
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≃ₜ
    ↥(CWComplex.skeleton X m : Set X) :=
  { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast; omega) hx⟩, hx⟩
      left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
      right_inv := fun ⟨x, _⟩ => rfl }
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val }

/-- The `TopCat`-isomorphism corresponding to `skeletonPreimageHomeo`. -/
def skeletonPreimageIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≅
    TopCat.of ↥(CWComplex.skeleton X m : Set X) :=
  TopCat.isoOfHomeo (skeletonPreimageHomeo m)

/-- For `k ≤ m`, the inclusion of preimages: viewing `X_k` and `X_m` as subsets of `X_{m+1}`,
the inclusion `(X_k \text{ in } X_{m+1}) ↪ (X_m \text{ in } X_{m+1})`. -/
def skeletonPreimageInclusion
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ⟶
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :=
  TopCat.ofHom ⟨fun ⟨y, hy⟩ => ⟨y, Topology.RelCWComplex.skeleton_mono
    (by norm_cast) hy⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The preimage-of-a-preimage homeomorphism identifying the nested preimage of `X_k`
inside `X_m ⊆ X_{m+1}` with the direct preimage of `X_k` inside `X_m`. -/
def skeletonPreimageSubHomeo
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    ↥(Subtype.val ⁻¹' (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :
      Set ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≃ₜ
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  { toEquiv := {
      toFun := fun ⟨⟨⟨x, hxm1⟩, hxm⟩, hxk⟩ => ⟨⟨x, hxm⟩, hxk⟩
      invFun := fun ⟨⟨x, hxm⟩, hxk⟩ => ⟨⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast; omega) hxm⟩, hxm⟩, hxk⟩
      left_inv := fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val }

/-- The `TopCat`-iso corresponding to `skeletonPreimageSubHomeo`. -/
def skeletonPreimageSubIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    TopCat.of ↥(Subtype.val ⁻¹' (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :
      Set ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≅
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  TopCat.isoOfHomeo (skeletonPreimageSubHomeo k m hkm)

/-- The induced isomorphism between singular chain complexes corresponding to
`skeletonPreimageIso`. -/
def skeletonPreimageChainIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m : ℕ) :
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(CWComplex.skeleton X m : Set X)) :=
  Excision.singularChainZ.mapIso (skeletonPreimageIso m)

/-- The induced isomorphism between singular chain complexes corresponding to
`skeletonPreimageSubIso`. -/
def skeletonPreimageSubChainIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹'
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :
      Set ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)))) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X))) :=
  Excision.singularChainZ.mapIso (skeletonPreimageSubIso k m hkm)

/-- The induced isomorphism on singular homology corresponding to `skeletonPreimageIso`. -/
def skeletonPreimageHomologyIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n m : ℕ) :
    (Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹'
      (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)))).homology n ≅
    SingularHomologyGroup n ↥(CWComplex.skeleton X m : Set X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (skeletonPreimageChainIso m)

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/-- The homeomorphism between two presentations of `X_k` as a subspace: as the preimage
of `X_k` inside `X_{m+1}` and as the preimage of `X_k` inside `X_m`. -/
def skeletonPreimageAkHomeo
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≃ₜ
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast) hx⟩, hx⟩
      invFun := fun ⟨⟨x, hxm⟩, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast; omega) hxm⟩, hx⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val }

/-- The `TopCat`-iso corresponding to `skeletonPreimageAkHomeo`. -/
def skeletonPreimageAkIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≅
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  TopCat.isoOfHomeo (skeletonPreimageAkHomeo k m hkm)

/-- The induced isomorphism between singular chain complexes corresponding to
`skeletonPreimageAkIso`. -/
def skeletonPreimageAkChainIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X))) :=
  Excision.singularChainZ.mapIso (skeletonPreimageAkIso k m hkm)

/-- For `n ≤ k ≤ m`, the relative homology `H_n(X_m, X_k) = 0`. Proved by induction on the
gap `m - k` using the triple exact sequence. -/
def CWComplex.SkeletonHomology.skelPairSubspaceMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) ⟶
    TopCat.of ↥(↑(CWComplex.skeleton X k : Set X) : Set X) :=
  TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the natural square for the pair maps: the subspace inclusion of
`X_k` (as a preimage in `X_m`) into `X_m`, then into `X`, equals the composition through
`X_k ⊆ X`. -/
lemma CWComplex.SkeletonHomology.skelPairSquare_comm
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) ≫
    CWComplex.SkeletonHomology.skeletonInclusion X m =
    CWComplex.SkeletonHomology.skelPairSubspaceMap k m ≫
    Excision.subspaceTopInclusion (↑(CWComplex.skeleton X k : Set X) : Set X) := by
  ext ⟨⟨_, _⟩, _⟩; rfl

/-- The induced map of relative singular chain complexes from the pair `(X_m, X_k)`
to the pair `(X, X_k)`. -/
noncomputable def CWComplex.SkeletonHomology.skelPairRelativeChainMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    Excision.relativeSingularChainComplex ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ⟶
    Excision.relativeSingularChainComplex X
      (↑(CWComplex.skeleton X k : Set X)) :=
  cokernel.map _ _
    (Excision.singularChainZ.map (CWComplex.SkeletonHomology.skelPairSubspaceMap k m))
    (Excision.singularChainZ.map (CWComplex.SkeletonHomology.skeletonInclusion X m))
    (by
      show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
        Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
      rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp,
        CWComplex.SkeletonHomology.skelPairSquare_comm])

/-- The induced map on relative singular homology
`H_n(X_m, X_k) → H_n(X, X_k)`. -/
noncomputable def CWComplex.SkeletonHomology.skelPairHomologyMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n k m : ℕ) :
    Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ⟶
    Excision.RelativeSingularHomologyGroup n X
      (↑(CWComplex.skeleton X k : Set X)) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (CWComplex.SkeletonHomology.skelPairRelativeChainMap k m)

/-- Every relative cycle of the pair `(X, X_k)` lifts to a relative cycle of some pair
`(X_m, X_k)` with `k ≤ m`, since singular chains are supported on compact (hence
finite-skeleton) subsets. -/
namespace CWComplex.SkeletonHomology

/-- **Proposition 16.2.** Combined statement: `H_q(X_k) = 0` for `k < q`, and the
inclusion induces an isomorphism `H_q(X_k) → H_q(X)` for `k > q`. -/
end CWComplex.SkeletonHomology

namespace CWHomology

/-- The cellular chain group `C_n(X)` packaged as an object of the category `AddCommGrpCat`. -/
noncomputable def cellularChainObj (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (CWComplex.cellularChains X n)

open Excision in
/-- The relative singular homology `H_q(X_n, X_{n-1})` of the CW pair, packaged as an
object of `AddCommGrpCat`. -/
noncomputable def relHomologySkeleton (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n q : ℕ) : AddCommGrpCat :=
  RelativeSingularHomologyGroup q
    (↥(CWComplex.skeleton X (n : ℕ∞) : Set X))
    (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X))

/-- The singular homology `H_q(X_n)` of the `n`-skeleton, packaged as an object of
`AddCommGrpCat`. -/
noncomputable def skeletonHomology (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n q : ℕ) : AddCommGrpCat :=
  SingularHomologyGroup q (↥(CWComplex.skeleton X (n : ℕ∞) : Set X))

/-- Excision-based identification: the relative homology `H_n(X_n, X_{n-1})` is
isomorphic to the finsupp `cell n →₀ ℤ`, exhibiting it as the free abelian group on
the set of `n`-cells. -/
noncomputable def skeletonConnectingHom (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    relHomologySkeleton X (n + 1) (n + 1) ⟶ skeletonHomology X n n := by

  let Y : Type := ↥(CWComplex.skeleton X (n + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X n : Set X)

  let hse := Excision.bottomSES_shortExact Y A
  let hRel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

  let delta := hse.δ (n + 1) n hRel

  let hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X n : Set X) :=
    { toEquiv := {
        toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
        invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
            (by norm_cast; omega) hx⟩, hx⟩
        left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
        right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X n : Set X) :=
    TopCat.isoOfHomeo hA_homeo

  let hhom_iso :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Excision.singularChainZ.mapIso hA_iso)

  exact delta ≫ hhom_iso.hom


/-- The map `H_n(X_n) → H_n(X_n, X_{n-1})` induced by the quotient of chain complexes. -/
noncomputable def skeletonInclusionMap (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonHomology X n n ⟶ relHomologySkeleton X n n :=


  HomologicalComplex.homologyMap
    (Excision.bottomSES
      (↥(CWComplex.skeleton X (n : ℕ∞) : Set X))
      (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X))).g n

/-- The cellular boundary squares to zero: `d_n ∘ d_{n+1} = 0`, making `C_*(X)` a chain
complex. -/
noncomputable def skeletonStepMap (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonHomology X n n ⟶ skeletonHomology X (n + 1) n :=
  CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n


/-- The identification of `H_n(X_{n+1})` with the cokernel of the connecting map (the
"H" of the left-homology data of the skeleton short complex). -/
structure IsCellularMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) : Prop where
  mapsTo_skeleton : ∀ (n : ℕ),
    Set.MapsTo f (CWComplex.skeleton X n :) (CWComplex.skeleton Y n :)

/-- The restriction of a cellular map `f : X → Y` to the `n`-skeletons, viewed as a
morphism `X_n ⟶ Y_n` in `TopCat`. -/
def cellularMapOnSkeleton
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X (n : ℕ∞) : Set X) ⟶
    TopCat.of ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y) :=
  TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨f x, hf.mapsTo_skeleton n hx⟩,
    Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) _⟩

/-- The restriction of a cellular map `f` to the previous-skeleton subspace, viewed as a
morphism between the preimages of `X_{n-1}` (in `X_n`) and `Y_{n-1}` (in `Y_n`). -/
def cellularMapOnPrevSkeleton
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) :
      Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ⟶
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) :
      Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) :=
  TopCat.ofHom ⟨fun ⟨⟨x, hxn⟩, hxprev⟩ =>
    ⟨⟨f x, hf.mapsTo_skeleton n hxn⟩, hf.mapsTo_skeleton (n - 1) hxprev⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact f.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- The naturality square between the inclusion of the previous-skeleton subspace into
the `n`-skeleton, and the cellular map restricted to skeletons, commutes. -/
lemma cellularMapSquare_comm
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) :
      Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ≫
    cellularMapOnSkeleton f hf n =
    cellularMapOnPrevSkeleton f hf n ≫
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) :
      Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) := by
  ext ⟨⟨_, _⟩, _⟩; rfl

/-- The induced map between relative singular chain complexes of the CW pairs
`(X_n, X_{n-1})` and `(Y_n, Y_{n-1})` arising from a cellular map. -/
def cellularRelativeChainMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X)) ⟶
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)
      (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y)) :=
  cokernel.map _ _
    (Excision.singularChainZ.map (cellularMapOnPrevSkeleton f hf n))
    (Excision.singularChainZ.map (cellularMapOnSkeleton f hf n))
    (by
      show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
        Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
      rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp,
        cellularMapSquare_comm])

/-- The induced map on relative singular homology
`H_n(X_n, X_{n-1}) → H_n(Y_n, Y_{n-1})` arising from a cellular map. -/
def relHomologySkeletonMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    relHomologySkeleton X n n ⟶ relHomologySkeleton Y n n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (cellularRelativeChainMap f hf n)

/-- The induced map on cellular chains `C_n(X) → C_n(Y)` arising from a cellular map,
obtained by transporting `relHomologySkeletonMap` along the cellular-chain
isomorphisms. -/
def skeletonAbsHomologyMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    skeletonHomology X n n ⟶ skeletonHomology Y n n :=
  HomologicalComplex.homologyMap
    (Excision.singularChainZ.map (cellularMapOnSkeleton f hf n)) n

/-- Naturality of the connecting homomorphism with respect to cellular maps. -/
noncomputable def singularHomologyMap (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SingularHomologyGroup n X ⟶ SingularHomologyGroup n Y :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)

/-- The map on cellular homology `H_n(C_*(X)) → H_n(C_*(Y))` induced by a cellular map. -/
noncomputable def skeletonHomologyMapInduced (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) :
    skeletonHomology X (n + 1) n ⟶ skeletonHomology Y (n + 1) n :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
    (cellularMapOnSkeleton f hf (n + 1))

/-- A CW complex has *only even cells* if there are no cells of odd dimension. -/
def HasOnlyEvenCells (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∀ k : ℕ, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) (2 * k + 1))
