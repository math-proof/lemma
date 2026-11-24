module
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part3
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
