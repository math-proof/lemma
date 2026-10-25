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
import Theorem.v1.Atlas.LieGroups.code.KostantTheorem


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
def kostant_cst_tensor :
    (TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace) ≃ₗ[ksd.invariantSubalgebra]
    SymmetricAlgebra R 𝔤 :=
  LinearEquiv.ofBijective (kostant_cst_mulMap ksd) (kostant_cst_mulMap_bijective ksd)

def kostant_Sg_tensor_decomposition :
    (TensorProduct R ksd.harmonicSubspace ksd.invariantSubalgebra) ≃ₗ[R]
    SymmetricAlgebra R 𝔤 :=
  (TensorProduct.comm R ksd.harmonicSubspace ksd.invariantSubalgebra).trans
    ((kostant_cst_tensor ksd).restrictScalars R)

def kostant_center_is_polynomial :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R]
    MvPolynomial (Fin ksd.rank) R :=
  ksd.pbwInvariantToCenter.symm.trans ksd.invariantPolynomial

def pbw_mulBilinear :
    (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₗ[R]
    ksd.harmonicSubspaceUEA →ₗ[R] UniversalEnvelopingAlgebra R 𝔤 where
  toFun z := {
    toFun := fun h => z.val * h.val
    map_add' := by intros x y; simp [mul_add]
    map_smul' := by intros r x; simp [Algebra.mul_smul_comm]
  }
  map_add' := by intros a b; ext h; simp [add_mul]
  map_smul' := by intros r a; ext h; simp [Algebra.smul_mul_assoc]

def pbw_mulMap_R :
    TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA →ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  TensorProduct.lift (pbw_mulBilinear ksd)

set_option synthInstance.maxHeartbeats 80000 in
def pbw_mulMap :
    TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA →ₗ[Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)]
    UniversalEnvelopingAlgebra R 𝔤 where
  toFun := pbw_mulMap_R ksd
  map_add' := (pbw_mulMap_R ksd).map_add
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a' h =>
      simp only [pbw_mulMap_R, TensorProduct.lift.tmul, pbw_mulBilinear,
                  RingHom.id_apply, TensorProduct.smul_tmul', LinearMap.coe_mk, AddHom.coe_mk]
      show (↑(a * a') : UniversalEnvelopingAlgebra R 𝔤) * (↑h : UniversalEnvelopingAlgebra R 𝔤) =
           ↑a * (↑a' * ↑h)
      rw [Subalgebra.coe_mul, mul_assoc]
    | add x y hx hy =>
      simp [map_add, hx, hy]

end
