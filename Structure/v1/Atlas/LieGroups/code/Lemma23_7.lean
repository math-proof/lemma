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
import Def.v1.Atlas.LieGroups.code.Lemma23_7


noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

structure IsProperRep_23_7
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop where
  lam_dominant : IsDominant_23_7 rd wg lam
  in_xi0 : IsInXi0_23_7 rd mu lam
  mu_minimal : ∀ (w : wg.W), w ∈ WeylStabilizer_23_7 wg lam →
    BruhatLE_23_7 rd mu (wg.dualAction w mu)

end
