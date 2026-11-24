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
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part5
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

/-- The relative chain map `S_*(U, U ∩ Kᶜ; R) → S_*(X, Kᶜ; R)` induced by the
inclusion of pairs `(U, U ∩ Kᶜ) → (X, Kᶜ)`; this is the chain-level excision
map. -/
def excisionPairChainMap (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    relSingChainCx R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R X Kᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (excisionSubspaceIncl X K U))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (excisionOpenIncl X U))
    (excisionPairIncl_comm R X K U)

/-- The induced map on relative homology
`H_n(U, U ∩ Kᶜ; R) → H_n(X, Kᶜ; R)` coming from the excision inclusion of
pairs. -/
def excisionForwardHomol (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (n : ℕ) :
    relSingularHomology R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) n ⟶
    relSingularHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (excisionPairChainMap R X K U) n

end FullyRelativeCapProduct
end
