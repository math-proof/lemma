/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section7
open ExactSequence


namespace HomologyCrossProduct

section SingularIntComplexConstruction

open AlgebraicTopologyI

/-- Integer-indexed boundary map on singular chains: for `n ≥ 1` it is the
usual boundary `S_{n.toNat}(X) → S_{n.toNat - 1}(X)` transported along the
identifications `n.toNat - 1 + 1 = n.toNat` and `n.toNat - 1 = (n - 1).toNat`;
for `n < 1` it is zero. This is the data used to view singular chains as an
`IntChainComplex`. -/
noncomputable def singularIntBoundary (X : Type) [TopologicalSpace X] (n : ℤ) :
    SingularChains n.toNat X →+ SingularChains (n - 1).toNat X :=
  if h : 1 ≤ n then
    have h1 : (n.toNat - 1 + 1) = n.toNat := by omega
    have h2 : (n.toNat - 1) = (n - 1).toNat := by omega
    h1 ▸ h2 ▸ boundaryMap (n.toNat - 1) X
  else 0

end SingularIntComplexConstruction
end HomologyCrossProduct
