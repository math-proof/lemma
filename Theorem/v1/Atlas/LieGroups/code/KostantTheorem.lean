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
import Def.v1.Atlas.LieGroups.code.KostantTheorem.Part2


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
theorem kostant_cst_mulMap_bijective :
    Function.Bijective (kostant_cst_mulMap ksd) := by


  have h_eq : (kostant_cst_mulMap ksd : TensorProduct R ksd.invariantSubalgebra
      ksd.harmonicSubspace → SymmetricAlgebra R 𝔤) = ksd.cst_equiv := by

    have h_lin_l : (kostant_cst_mulMap_R ksd : TensorProduct R ksd.invariantSubalgebra
        ksd.harmonicSubspace →ₗ[R] SymmetricAlgebra R 𝔤) =
        ksd.cst_equiv.toLinearMap := by
      ext a h
      simp only [kostant_cst_mulMap_R, kostant_cst_mulBilinear]
      exact (ksd.cst_equiv_apply_tmul a h).symm
    ext x
    exact congr_fun (congr_arg DFunLike.coe h_lin_l) x
  rw [h_eq]
  exact ksd.cst_equiv.bijective

end
