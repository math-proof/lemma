/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Theorem.v1.Atlas.LieGroups.code.PBW
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Theorem.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] WeylGroupData.instGroup WeylGroupData.instFintype

set_option maxHeartbeats 400000 in
def betaMap (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos)) →ₗ[R]
    UniversalEnvelopingAlgebra R Δ.𝔥 := by
  apply TensorProduct.lift


  let inner : TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
      (UniversalEnvelopingAlgebra R Δ.𝔫_pos) →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
    TensorProduct.lift
      (((LinearMap.lsmul R (UniversalEnvelopingAlgebra R Δ.𝔥)).comp
        (augmentation R Δ.𝔫_pos).toLinearMap).flip)

  exact ((LinearMap.lsmul R _).comp (augmentation R Δ.𝔫_neg).toLinearMap).flip inner

def HarishChandraMap (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
  (betaMap Δ).comp (pbwTriangularIso Δ).symm.toLinearMap

end
