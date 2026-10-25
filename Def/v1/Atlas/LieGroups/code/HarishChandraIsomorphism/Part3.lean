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
import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism
-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] WeylGroupData.instGroup WeylGroupData.instFintype

def WeylGroupData.invariantSubalgebra {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) :
    Subalgebra R (UniversalEnvelopingAlgebra R Δ.𝔥) :=
  Subalgebra.invariants wg.W wg.algAction

def WeylGroupData.shiftedAction {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) (w : wg.W) (mu : Δ.𝔥 →ₗ[R] R) : Δ.𝔥 →ₗ[R] R :=
  wg.dualAction w (mu + wg.ρ) - wg.ρ

def PositiveRootData.sumPosRoots {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (rd : PositiveRootData Δ) : Δ.𝔥 →ₗ[R] R :=
  ∑ α ∈ rd.posRoots, α

def augmentation (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)


/-- PBW triangular factorization isomorphism (olean stub). -/
noncomputable def pbw_triangular_iso (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  sorry

def pbwTriangularIso (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  pbw_triangular_iso R 𝔤 Δ


end
