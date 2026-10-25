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
import Structure.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology


namespace ContractibleHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Corollary 5.7**. The singular homology of a contractible space $X$ is given by
$H_0(X; \mathbb{Z}) \cong \mathbb{Z}$ and $H_n(X; \mathbb{Z}) = 0$ for $n \neq 0$. -/
def singularHomologyOfContractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] : SingularHomologyOfContractible X where
  isoZero := singularHomologyZeroIsoZ_of_contractible X
  isZero_pos := singularHomology_isZero_of_contractible X

/-- The augmentation map $\varepsilon : H_0(Z; \mathbb{Z}) \to \mathbb{Z}$, defined as the
composition of the map induced by $Z \to \mathrm{pt}$ with the canonical identification
$H_0(\mathrm{pt}; \mathbb{Z}) \cong \mathbb{Z}$. -/
def augmentationH₀ (Z : Type) [TopologicalSpace Z] :
    ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Z) ⟶
      AddCommGrpCat.of ℤ :=
  ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).map
    (TopCat.isTerminalPUnit.from (TopCat.of Z)) ≫
  (singularHomologyFunctorZeroOfTotallyDisconnectedSpace _ _ _).hom ≫
  (coproductUniqueIso _).hom

end
end ContractibleHomology
