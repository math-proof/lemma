/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Goal139_KLProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections


noncomputable section

universe u

variable {R : Type u} [Field R] [IsAlgClosed R] [CharZero R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

end
