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


noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

def IsInXi0_23_7
    (rd : PositiveRootData Δ) (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    lam - mu = ∑ α ∈ rd.posRoots, (c α) • α

def WeylStabilizer_23_7
    (wg : WeylGroupData Δ) (lam : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w | wg.dualAction w lam = lam}

def BruhatLE_23_7
    (rd : PositiveRootData Δ) (mu nu : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ),
    nu - mu = ∑ α ∈ rd.posRoots, (c α) • α

def IsDominant_23_7
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ) (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), BruhatLE_23_7 rd (wg.dualAction w lam) lam

end
