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
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part4
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

/-- The short complex of relative singular chain complexes for the triple
`(X, Lᶜ, Kᶜ)`, namely
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)`. -/
def tripleShortComplex (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk
    (tripleInclChainMap R X K L)
    (restrictionChainMap R X K L h)
    (tripleInclChainMap_comp_restrictionChainMap_eq_zero R X K L h)

end FullyRelativeCapProduct
end
