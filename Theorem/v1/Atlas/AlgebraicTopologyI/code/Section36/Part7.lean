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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part10
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- Commutativity of the square of inclusions relating the pair
`(U \ L, (U \ L) ∩ Kᶜ)` to `(Lᶜ, Lᶜ ∩ Kᶜ)`, in `TopCat`. -/
lemma localityIncl_comm_topcat (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    subtypeIncl (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      localityBigIncl X L pair =
    localitySubIncl X K L pair ≫
      subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- Chain-level version of `localityIncl_comm_topcat`: the induced square of
chain maps between singular chain complexes commutes. -/
lemma localityIncl_comm_chain (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    inclChainMap R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (localityBigIncl X L pair) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (localitySubIncl X K L pair) ≫
      inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
  simp only [inclChainMap, ← Functor.map_comp, localityIncl_comm_topcat X K L pair]

end FullyRelativeCapProduct
end
