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
import Structure.v1.Atlas.LieGroups.code.KostantTheorem


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

def KostantSetupData.isDominant
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (μ : ksd.P) : Prop :=
  ∀ i : Fin ksd.rank, 0 ≤ ksd.pairingCoroot μ i

def KostantSetupData.dotAction
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (w : ksd.W) (μ : ksd.P) : ksd.P :=
  ksd.actionW w (μ + ksd.rho) - ksd.rho

variable [LieAlgebra.IsSemisimple R 𝔤]

variable (ksd : @KostantSetupData R _ 𝔤 _ _ _)

def KostantSetupData.hilbertSeriesHomDual
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (wt : ksd.P) : PowerSeries ℤ :=
  (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
  (concreteCT_posRoots_lambda ksd.roots ksd.posRoots wt : PowerSeries ℤ)

def KostantSetupData.actualHilbertSeriesHom
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (wt : ksd.P) : PowerSeries ℤ :=
  gradedHilbertSeries (ksd.gradedHomDim wt)

def kostant_cst_mulBilinear :
    ksd.invariantSubalgebra →ₗ[R] ksd.harmonicSubspace →ₗ[R] SymmetricAlgebra R 𝔤 where
  toFun a := {
    toFun := fun h => a.val * h.val
    map_add' := by intros x y; simp [mul_add]
    map_smul' := by intros r x; simp [Algebra.mul_smul_comm]
  }
  map_add' := by intros a b; ext h; simp [add_mul]
  map_smul' := by intros r a; ext h; simp [Algebra.smul_mul_assoc]

def kostant_cst_mulMap_R :
    TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace →ₗ[R]
    SymmetricAlgebra R 𝔤 :=
  TensorProduct.lift (kostant_cst_mulBilinear ksd)

set_option synthInstance.maxHeartbeats 80000 in
def kostant_cst_mulMap :
    TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace →ₗ[ksd.invariantSubalgebra]
    SymmetricAlgebra R 𝔤 where
  toFun := kostant_cst_mulMap_R ksd
  map_add' := (kostant_cst_mulMap_R ksd).map_add
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a' h =>
      simp only [kostant_cst_mulMap_R, TensorProduct.lift.tmul, kostant_cst_mulBilinear,
                  RingHom.id_apply, TensorProduct.smul_tmul', LinearMap.coe_mk, AddHom.coe_mk]
      show (↑(a * a') : SymmetricAlgebra R 𝔤) * (↑h : SymmetricAlgebra R 𝔤) =
           ↑a * (↑a' * ↑h)
      rw [Subalgebra.coe_mul, mul_assoc]
    | add x y hx hy =>
      simp [map_add, hx, hy]

end
