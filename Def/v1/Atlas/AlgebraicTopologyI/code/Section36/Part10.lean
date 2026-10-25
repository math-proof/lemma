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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section36.Part6
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The inverse of the excision isomorphism, providing a linear map
`H_n(X, Kᶜ; R) → H_n(U, U ∩ Kᶜ; R)` that lifts a relative homology class on
`(X, Kᶜ)` to a class supported in the open neighbourhood `U` of `K`. -/
def excisionInverseHomol
    (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X)
    (hK : K ⊆ ↑U) (n : ℕ) :
    (relSingularHomology R X Kᶜ n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) n : Type _) := by
  classical
  haveI := excisionForwardHomol_isIso R X K U hK n
  exact (inv (excisionForwardHomol R X K U n)).hom

/-- The inclusion `U \ L ↪ Lᶜ` as a morphism in `TopCat`, used to compare
`(U \ L, (U \ L) ∩ Kᶜ)` with `(Lᶜ, Lᶜ ∩ Kᶜ)`. -/
def localityBigIncl (X : TopCat.{0}) {K : Set X} (L : Set X)
    (pair : OpenNbhdPair K L) :
    TopCat.of ↑(pair.U.1 \ L) ⟶ TopCat.of (Lᶜ : Set X) :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The inclusion `(U \ L) ∩ Kᶜ ↪ Lᶜ ∩ Kᶜ`, viewed as a morphism in `TopCat`
between the relativizing subspaces. -/
def localitySubIncl (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair.U.1 \ L))) ⟶
    TopCat.of (complementInComplement X K L) :=
  ⟨fun ⟨⟨x, hxUL⟩, hxK⟩ => ⟨⟨x, hxUL.2⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

end FullyRelativeCapProduct
end
