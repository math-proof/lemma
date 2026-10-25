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
import Structure.v1.Atlas.LieGroups.code.DufloJoseph


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsInHCBimod.ofEvalHC (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hchar : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam) (evalHC Δ wg mu)) :
    IsInHCBimod M (evalHC Δ wg lam) (evalHC Δ wg mu) :=
  ⟨hHC, hchar⟩


def stabilizerOfWeight (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) (γ : Δ.𝔥 →ₗ[R] R) : Subgroup wg.W where
  carrier := { w | wg.dualAction w γ = γ }
  one_mem' := by
    show wg.dualAction 1 γ = γ
    exact wg.dualAction_one γ
  mul_mem' := by
    intro a b ha hb
    show wg.dualAction (a * b) γ = γ
    rw [wg.dualAction_mul, hb, ha]
  inv_mem' := by
    intro a ha
    show wg.dualAction a⁻¹ γ = γ
    have h := wg.dualAction_mul a⁻¹ a γ
    rw [inv_mul_cancel, wg.dualAction_one, ha] at h
    exact h.symm

def equivModStab (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (γ : Δ.𝔥 →ₗ[R] R) (lam₁ lam₂ : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ w ∈ stabilizerOfWeight Δ wg γ, wg.dualAction w lam₁ = lam₂

end
