/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Lemma23_7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part7
import Lemma.Int.IsDirectSummand
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
import Structure.v1.Atlas.LieGroups.code.Lemma23_7.Part2


noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

def maximalSupport_23_7 [LE R]
    {wg : WeylGroupData Δ} (B : BilinFormData_23_7 wg) (S : SupportData_23_7 wg) :
    Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | p ∈ S.support ∧
    ∀ q ∈ S.support, B.normSq (q.2 - q.1) ≤ B.normSq (p.2 - p.1)}

end
