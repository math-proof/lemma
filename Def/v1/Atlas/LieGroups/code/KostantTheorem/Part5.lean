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
public import Abbrev.v1.Atlas.LieGroups.code.KostantTheorem


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

include ksd in
def kostant_Ug_tensor_decomposition :
    (TensorProduct R ksd.harmonicSubspaceUEA
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)).toSubmodule) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  (TensorProduct.comm R ksd.harmonicSubspaceUEA
    (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)).toSubmodule).trans
    ((pbwTensorEquivUEA ksd).restrictScalars R)

def KostantFqSingleFactor (q : ℝ) (z : ℂ) : ℂ :=
  (1 - z) / (1 - (q : ℂ) * z)

def KostantFqProd {ι T : Type*} (posRoots : Finset ι) (φ : ι → T → ℂ)
    (q : ℝ) (x : T) : ℂ :=
  ∏ α ∈ posRoots, KostantFqSingleFactor q (φ α x)

end
