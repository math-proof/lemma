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
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology


namespace ContractibleHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- For a contractible space $X$ and $n \neq 0$, the singular homology $H_n(X; \mathbb{Z})$
vanishes. Combined with `singularHomologyZeroIsoZ_of_contractible`, this yields
Corollary 5.7. -/
theorem singularHomology_isZero_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) := by
  let e := Classical.choice (ContractibleSpace.hequiv_unit X)
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hn).of_iso
    (singularHomologyIsoOfHomotopyEquiv e n)

end
end ContractibleHomology
