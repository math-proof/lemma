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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part2
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


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
