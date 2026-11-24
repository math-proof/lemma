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
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part2
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

/-- The induced chain map on relative singular chain complexes,
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(X, Kᶜ; R)`, coming from the inclusions of the
triple `(Lᶜ ∩ Kᶜ) ⊆ Lᶜ ⊆ X` and `(Lᶜ ∩ Kᶜ) ⊆ Kᶜ ⊆ X`. -/
def tripleInclChainMap (X : TopCat.{0}) (K L : Set X) :
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ⟶
    relSingChainCx R X Kᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (complToComplement X K L))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (subtypeIncl X Lᶜ))
    (tripleIncl_comm_chain R X K L)

/-- The induced map on relative homology,
`H_q(Lᶜ, Lᶜ ∩ Kᶜ; R) → H_q(X, Kᶜ; R)`, coming from the inclusion of pairs
`(Lᶜ, Lᶜ ∩ Kᶜ) → (X, Kᶜ)`. -/
def homolTripleInclusion
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R (TopCat.of (Lᶜ : Set X))
      (complementInComplement X K L) q ⟶
      relSingularHomology R X Kᶜ q :=
  HomologicalComplex.homologyMap (tripleInclChainMap R X K L) q

end FullyRelativeCapProduct
end
