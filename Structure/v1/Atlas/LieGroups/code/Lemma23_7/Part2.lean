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
import Def.v1.Atlas.LieGroups.code.Lemma23_7.Part2


noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

structure BilinFormData_23_7
    (wg : WeylGroupData Δ) [LE R] where
  normSq : (Δ.𝔥 →ₗ[R] R) → R
  weyl_invariant : ∀ (w : wg.W) (v : Δ.𝔥 →ₗ[R] R),
    normSq (wg.dualAction w v) = normSq v
  normSq_sub_weyl_invariant : ∀ (w : wg.W) (a b : Δ.𝔥 →ₗ[R] R),
    normSq (wg.dualAction w a - wg.dualAction w b) = normSq (a - b)

structure SupportData_23_7
    (wg : WeylGroupData Δ) where
  support : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
  weyl_equivariant : ∀ (w : wg.W) (p : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)),
    p ∈ support → (wg.dualAction w p.1, wg.dualAction w p.2) ∈ support

end
