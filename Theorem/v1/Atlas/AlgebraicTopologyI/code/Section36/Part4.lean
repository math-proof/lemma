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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part6
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

/-- The composition `tripleInclChainMap ≫ restrictionChainMap` vanishes,
expressing the chain-level exactness needed to obtain the short exact
sequence of relative chain complexes for the triple `(X, Lᶜ, Kᶜ)`. -/
lemma tripleInclChainMap_comp_restrictionChainMap_eq_zero
    (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    tripleInclChainMap R X K L ≫ restrictionChainMap R X K L h = 0 := by
  simp only [tripleInclChainMap, restrictionChainMap, relSingChainCx]

  apply coequalizer.hom_ext
  simp only [cokernel.π_desc_assoc, comp_zero, Category.assoc]


  rw [cokernel.π_desc]
  simp only [Category.id_comp]


  show inclChainMap R X Lᶜ ≫ cokernel.π (inclChainMap R X Lᶜ) = 0
  exact cokernel.condition _

end FullyRelativeCapProduct
end
