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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology


namespace ContractibleHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Packaged data of singular homology for a contractible space: an isomorphism
$H_0(X; \mathbb{Z}) \cong \mathbb{Z}$ together with a proof that $H_n(X; \mathbb{Z}) = 0$
for $n \neq 0$. -/
structure SingularHomologyOfContractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] where
  isoZero :
    ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
      AddCommGrpCat.of ℤ
  isZero_pos : ∀ (n : ℕ), n ≠ 0 →
    IsZero (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

end
end ContractibleHomology
