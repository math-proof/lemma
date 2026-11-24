module
public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Theorem.Int.Any_All_Eq.of.LeKer_Ker.Surjective
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Def.v1.Atlas.LieGroups.code.KostantTheorem.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
