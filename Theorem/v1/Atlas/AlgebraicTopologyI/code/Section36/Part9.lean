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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part12
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- Compatibility square in `TopCat` between subspace and big-pair inclusions
for nested neighbourhood pairs, on the `q`-side. -/
lemma nbhdIncl_comm_topcat_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    subtypeIncl (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      nbhdBigIncl_q pair₁ pair₂ h =
    nbhdSubIncl_q pair₁ pair₂ h ≫
      subtypeIncl (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _, _⟩, _⟩
  rfl

/-- Chain-level version of `nbhdIncl_comm_topcat_q`: the corresponding square
of chain maps commutes on the `q`-side. -/
lemma nbhdIncl_comm_chain_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    inclChainMap R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdBigIncl_q pair₁ pair₂ h) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdSubIncl_q pair₁ pair₂ h) ≫
      inclChainMap R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
  simp only [inclChainMap, ← Functor.map_comp, nbhdIncl_comm_topcat_q pair₁ pair₂ h]

end FullyRelativeCapProduct
end
