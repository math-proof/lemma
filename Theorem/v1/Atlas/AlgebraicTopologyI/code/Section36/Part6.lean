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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part9
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

/-- Excision at the level of abelian groups: after forgetting the
`R`-module structure, the chain map `excisionPairChainMap` is a quasi-iso at
degree `n`. -/
theorem excisionPairChainMap_quasiIsoAt (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (hK : K ⊆ ↑U) (n : ℕ) :
    QuasiIsoAt (excisionPairChainMap R X K U) n := by
  have := (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
    (excisionPairChainMap R X K U)
    (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) n).mp
  apply this
  exact excisionPairChainMap_quasiIsoAt_forget₂ R X K U hK n


/-- The excision map on homology
`H_n(U, U ∩ Kᶜ; R) → H_n(X, Kᶜ; R)` is an isomorphism when `K ⊆ U`. -/
theorem excisionForwardHomol_isIso (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (hK : K ⊆ ↑U) (n : ℕ) :
    IsIso (excisionForwardHomol R X K U n) := by
  have hqi := excisionPairChainMap_quasiIsoAt R X K U hK n
  rwa [quasiIsoAt_iff_isIso_homologyMap] at hqi

end FullyRelativeCapProduct
end
