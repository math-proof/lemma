/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Homology.AlternatingConst
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section5
open CategoryTheory

universe u₀


namespace HomotopyInvariance

open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable {f₀ f₁ : C ⟶ D}

/-- A chain homotopy equivalence between chain complexes `C` and `D` induces an
isomorphism on `i`-th homology (a consequence of Lemma 5.10). -/
noncomputable def homotopyEquivHomologyIso
    (e : HomotopyEquiv C D) (i : ι)
    [C.HasHomology i] [D.HasHomology i] :
    C.homology i ≅ D.homology i where
  hom := homologyMap e.hom i
  inv := homologyMap e.inv i
  hom_inv_id := by
    rw [← homologyMap_comp,
      chainHomotopy_homologyMap_eq e.homotopyHomInvId,
      homologyMap_id]
  inv_hom_id := by
    rw [← homologyMap_comp,
      chainHomotopy_homologyMap_eq e.homotopyInvHomId,
      homologyMap_id]

universe w₁ v₁ u₁

/-- **Corollary 5.5**. A homotopy equivalence of topological spaces `X ≃ Y` induces an
isomorphism on `n`-th singular homology (with coefficients in `R`). -/
noncomputable def homotopyEquivHomologyIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y)
    {C : Type*} [Category C] [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of Y) := by
  let F := ((singularHomologyFunctor C n).obj R)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨F.map f, F.map g, ?_, ?_⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨H⟩ := e.left_inv
    have hfg : f ≫ g = TopCat.ofHom (e.invFun.comp e.toFun) := by ext; rfl
    have hid : 𝟙 (TopCat.of X) = TopCat.ofHom (ContinuousMap.id X) := by ext; rfl
    rw [hfg, hid]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨H⟩ := e.right_inv
    have hgf : g ≫ f = TopCat.ofHom (e.toFun.comp e.invFun) := by ext; rfl
    have hid : 𝟙 (TopCat.of Y) = TopCat.ofHom (ContinuousMap.id Y) := by ext; rfl
    rw [hgf, hid]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R n

end HomotopyInvariance
