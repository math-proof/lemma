/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10.Part10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

section SuspensionIsoProof

open AlgebraicTopology

noncomputable section

/-- Local copy of `pairSES_shortExact` for the suspension-isomorphism proof. -/
def suspPairSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (suspPairSES X A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- Local copy of `pairδIso` for the suspension-isomorphism proof. -/
noncomputable def suspPairδIso (X : Type) [TopologicalSpace X] (A : Set X)
    (q : ℕ)
    (hi : IsZero ((suspPairSES X A).X₂.homology (q + 1)))
    (hj : IsZero ((suspPairSES X A).X₂.homology q)) :
    (suspPairSES X A).X₃.homology (q + 1) ≅ (suspPairSES X A).X₁.homology q :=
  (suspPairSES_shortExact X A).δIso (q + 1) q (by rw [ComplexShape.down_Rel]) hi hj


/-- Local copy of `bdryToSphereIso`: the identification `∂D^{n+1} ≅ S^n`. -/
noncomputable def suspBdryToSphereIso (n : ℕ) :
    TopCat.of ↥(diskBoundarySubset (n + 1)) ≅ TopCat.of (Sphere n) where
  hom := TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hsp⟩ => ⟨x, hsp⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩
  inv := TopCat.ofHom ⟨fun ⟨x, hsp⟩ => ⟨⟨x, Metric.sphere_subset_closedBall hsp⟩, hsp⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _⟩
  hom_inv_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨⟨_, _⟩, _⟩; rfl
  inv_hom_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨_, _⟩; rfl

end
end SuspensionIsoProof
end SphereHomology
