/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Category.Grp.Abelian
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section16


namespace CWComplex

variable (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

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

end CWComplex.SkeletonHomology
end
