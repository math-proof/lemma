/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part3
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The chain map between relative singular chain complexes
`S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)`, induced by enlarging the relative subspace
from `Kᶜ` to `Lᶜ` (assuming `Kᶜ ⊆ Lᶜ`, i.e. `L ⊆ K`). -/
def restrictionChainMap (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    relSingChainCx R X Kᶜ ⟶ relSingChainCx R X Lᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (subsetInclusion X Kᶜ Lᶜ h))
    (𝟙 _)
    (restriction_comm_chain R X K L h)

/-- The restriction map `H_q(X, Kᶜ; R) → H_q(X, Lᶜ; R)` induced by enlarging
the relative subspace from `Kᶜ` to `Lᶜ` (defined to be zero if `Kᶜ ⊄ Lᶜ`). -/
def homolRestriction
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R X Kᶜ q ⟶ relSingularHomology R X Lᶜ q := by
  classical
  exact if h : (Kᶜ : Set X) ⊆ Lᶜ
    then HomologicalComplex.homologyMap (restrictionChainMap R X K L h) q
    else 0

end FullyRelativeCapProduct
end
