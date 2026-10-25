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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part4
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- Commutativity of the square of inclusions
`(Lᶜ ∩ Kᶜ) ↪ Lᶜ ↪ X` and `(Lᶜ ∩ Kᶜ) ↪ Kᶜ ↪ X` in `TopCat`. -/
lemma tripleIncl_comm_topcat (X : TopCat.{0}) (K L : Set X) :
    subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫
      subtypeIncl X Lᶜ =
    complToComplement X K L ≫ subtypeIncl X Kᶜ := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- The chain-level version of `tripleIncl_comm_topcat`: the corresponding
square of chain maps between singular chain complexes commutes. -/
lemma tripleIncl_comm_chain (X : TopCat.{0}) (K L : Set X) :
    inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subtypeIncl X Lᶜ) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (complToComplement X K L) ≫
      inclChainMap R X Kᶜ := by
  simp only [inclChainMap, ← Functor.map_comp, tripleIncl_comm_topcat X K L]

end FullyRelativeCapProduct
end
