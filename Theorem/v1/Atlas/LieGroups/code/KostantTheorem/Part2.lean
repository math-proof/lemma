/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.SimpleModule.Basic
import Def.v1.Atlas.LieGroups.code.KostantTheorem.Part3


noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

variable {P' : Type*} [DecidableEq P'] [AddCommGroup P']

attribute [instance] KostantSetupData.instCartan

attribute [instance] KostantSetupData.instLieRingModuleSg KostantSetupData.instLieModuleSg

attribute [instance] KostantSetupData.instGroup KostantSetupData.instFintype

attribute [instance] KostantSetupData.instAddCommGroup_P KostantSetupData.instDecEq_P

attribute [instance] KostantSetupData.instFreeHarmonic

variable [LieAlgebra.IsSemisimple R 𝔤]

variable (ksd : @KostantSetupData R _ 𝔤 _ _ _)

set_option synthInstance.maxHeartbeats 80000 in
theorem pbw_mulMap_bijective :
    Function.Bijective (pbw_mulMap ksd) := by

  show Function.Bijective (pbw_mulMap_R ksd)

  let α : ksd.invariantSubalgebra ≃ₗ[R]
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :=
    ksd.pbwInvariantToCenter.toLinearEquiv
  let β : ksd.harmonicSubspace ≃ₗ[R] ksd.harmonicSubspaceUEA := ksd.pbwHarmonicEquiv
  let τ : TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace ≃ₗ[R]
      TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
        ksd.harmonicSubspaceUEA :=
    TensorProduct.congr α β
  let σ := ksd.pbwSymmEquiv

  have hcompat : ∀ (x : TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace),
      pbw_mulMap_R ksd (τ x) = σ (kostant_cst_mulMap_R ksd x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a h =>

      show pbw_mulMap_R ksd (TensorProduct.congr α β (a ⊗ₜ[R] h)) = σ (kostant_cst_mulMap_R ksd (a ⊗ₜ[R] h))
      rw [TensorProduct.congr_tmul]
      simp only [pbw_mulMap_R, kostant_cst_mulMap_R, TensorProduct.lift.tmul,
        pbw_mulBilinear, kostant_cst_mulBilinear, LinearMap.coe_mk, AddHom.coe_mk]
      exact (ksd.pbwSymmCompat a h).symm
    | add x y hx hy => simp [map_add, hx, hy]

  have hfactor : ∀ y, pbw_mulMap_R ksd y =
      σ (kostant_cst_mulMap_R ksd (τ.symm y)) := by
    intro y
    rw [← hcompat, LinearEquiv.apply_symm_apply]


  have hcst : Function.Bijective (kostant_cst_mulMap_R ksd) := by
    show Function.Bijective (kostant_cst_mulMap ksd)
    exact kostant_cst_mulMap_bijective ksd

  constructor
  · intro a b hab
    rw [hfactor a, hfactor b] at hab
    have h1 := σ.injective hab
    have h2 := hcst.1 h1
    exact τ.symm.injective h2
  · intro y
    obtain ⟨s, hs⟩ := σ.surjective y
    obtain ⟨t, ht⟩ := hcst.2 s
    exact ⟨τ t, by rw [hfactor, LinearEquiv.symm_apply_apply, ht, hs]⟩

end
