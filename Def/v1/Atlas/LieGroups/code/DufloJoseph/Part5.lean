/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Lemma.Fin.Any_Eq.of.Ne_0
import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
import Theorem.v1.Atlas.LieGroups.code.DufloJoseph.Part4


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def ueaIncl_neg (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔫_neg.incl : Δ.𝔫_neg →ₗ⁅R⁆ 𝔤))

def ueaIncl_pos (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔫_pos.incl : Δ.𝔫_pos →ₗ⁅R⁆ 𝔤))

noncomputable def multMap_xi
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R) :
    TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) →ₗ[R]
    MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b =>
            MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ))
              (ueaIncl_neg Δ a * ueaIncl_pos Δ b)
          map_add' := fun b₁ b₂ => by simp [mul_add, map_add]
          map_smul' := fun r b => by simp [map_smul] }
      map_add' := fun a₁ a₂ => by ext b; simp [add_mul, map_add]
      map_smul' := fun r a => by ext b; simp [map_smul] }

noncomputable def multMap_ug
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) →ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => ueaIncl_neg Δ a * ueaIncl_pos Δ b
          map_add' := fun b₁ b₂ => by simp [mul_add]
          map_smul' := fun r b => by simp }
      map_add' := fun a₁ a₂ => by ext b; simp [add_mul]
      map_smul' := fun r a => by ext b; simp }

def ueaIncl_h (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔥 →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔥.incl : Δ.𝔥 →ₗ⁅R⁆ 𝔤))

end
