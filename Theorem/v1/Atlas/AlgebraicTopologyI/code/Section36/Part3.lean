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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part5
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

/-- Compatibility square needed to define the restriction chain map
`S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)` when `Kᶜ ⊆ Lᶜ`. -/
lemma restriction_comm_chain (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    inclChainMap R X Kᶜ ≫ 𝟙 _ =
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subsetInclusion X Kᶜ Lᶜ h) ≫ inclChainMap R X Lᶜ := by
  simp only [Category.comp_id, inclChainMap, ← Functor.map_comp,
    subtypeIncl_factor X Kᶜ Lᶜ h]

end FullyRelativeCapProduct
end
