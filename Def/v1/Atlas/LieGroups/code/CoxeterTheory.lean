/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Lemma.Int.IsInQPlus0
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
import Structure.v1.Atlas.LieGroups.code.CoxeterTheory


noncomputable section

open scoped BigOperators

namespace CoxeterGroupData

variable (C : CoxeterGroupData)

def IsReducedWord (word : List C.W) : Prop :=
  (∀ s ∈ word, s ∈ C.simpleReflections) ∧ word.length = C.length word.prod

def weylLength (wg : WeylGroupData Δ) (C : CoxeterGroupData)
    (rd : PositiveRootData Δ) (compat : CoxeterWeylCompatibility C rd wg)
    (w : wg.W) : ℕ :=
  C.length (compat.ι.symm w)

end WeylGroupData

namespace RootSystemWithReflections

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

variable {rd : PositiveRootData Δ}

variable {wg : WeylGroupData Δ}

def inversions (_rs : RootSystemWithReflections rd wg)
    (w : wg.W) : Finset (Δ.𝔥 →ₗ[R] R) := by
  classical
  exact rd.posRoots.filter (fun α => -(wg.dualAction w α) ∈ rd.posRoots)

end RootSystemWithReflections
end
