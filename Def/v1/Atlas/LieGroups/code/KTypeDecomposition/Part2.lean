/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Lie.OfAssociative
import Theorem.v1.Atlas.LieGroups.code.KTypeDecomposition
attribute [local instance 100] LieRing.ofAssociativeRing

open Module

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

def ktypeSet (M : SL2GKModule 𝔤 K 𝔨 Ad V) : Set ℤ :=
  {n : ℤ | M.weightSpace n ≠ ⊥}

end SL2GKModule
end
