/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ContractibleHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian


namespace ContractibleHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homotopy invariance of singular homology: a homotopy equivalence $X \simeq Y$
induces an isomorphism $H_n(X; \mathbb{Z}) \cong H_n(Y; \mathbb{Z})$ for every $n$. -/
def singularHomologyIsoOfHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Y) := by
  let F := ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ))
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have H_left : TopCat.Homotopy (f ≫ g) (CategoryStruct.id (TopCat.of X)) :=
    Classical.choice e.left_inv
  have H_right : TopCat.Homotopy (g ≫ f) (CategoryStruct.id (TopCat.of Y)) :=
    Classical.choice e.right_inv
  exact
    { hom := F.map f
      inv := F.map g
      hom_inv_id := by
        rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H_left _ n
      inv_hom_id := by
        rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H_right _ n }

/-- For a contractible space $X$, the augmentation gives an isomorphism
$H_0(X; \mathbb{Z}) \cong \mathbb{Z}$. Used in the proof of Corollary 5.7. -/
def singularHomologyZeroIsoZ_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] :
    ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
      AddCommGrpCat.of ℤ :=
  let e := Classical.choice (ContractibleSpace.hequiv_unit X)
  singularHomologyIsoOfHomotopyEquiv e 0 ≪≫
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace _ _ _ ≪≫
    coproductUniqueIso _

end
end ContractibleHomology
