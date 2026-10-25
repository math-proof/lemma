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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section16
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI


noncomputable section

namespace CWComplex.SkeletonHomology

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


end CWHomology
end CWComplex.SkeletonHomology
end
