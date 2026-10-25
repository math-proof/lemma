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
import Class.v1.Atlas.AlgebraicTopologyI.code.Section36
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

def excisionOpenIncl (X : TopCat.{0}) (U : TopologicalSpace.Opens X) :
    TopCat.of ↑U.1 ⟶ X :=
  subtypeIncl X U.1

/-- The inclusion `U ∩ Kᶜ ↪ Kᶜ` of subspaces of `X`, used to set up the
excision map for the pair `(X, Kᶜ)` relative to an open neighbourhood of `K`. -/
def excisionSubspaceIncl (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑U.1)) ⟶ TopCat.of (Kᶜ : Set X) :=
  ⟨fun ⟨⟨x, _⟩, hxK⟩ => ⟨x, hxK⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

end FullyRelativeCapProduct
end
