/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Real.IsSmoothVector0
import Lemma.Complex.Eq_Sum_Mul
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
import Def.v1.Atlas.LieGroups.code.IsotypicPeterWeyl.Part3
import Theorem.v1.Atlas.LieGroups.code.SmoothVectorsProps
import Def.v1.Atlas.LieGroups.code.CompactMeasures
import Structure.v1.Atlas.LieGroups.code.PlancherelCompact
set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory


noncomputable section

namespace PlancherelCompact

attribute [instance] IrrFinDimRep.instNormedAddCommGroup
  IrrFinDimRep.instInnerProductSpace IrrFinDimRep.instFiniteDimensional
  IrrFinDimRep.instCompleteSpace IrrFinDimRep.nontrivial

def IrrFinDimRep.dim {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] (ρ : IrrFinDimRep K) : ℕ :=
  Module.finrank ℂ ρ.carrier

def IrrFinDimRep.repFourierCoeff {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f : K → ℂ) : ρ.carrier →L[ℂ] ρ.carrier :=
  ∫ k, f k • ρ.rep.toMonoidHom k

def IrrFinDimRep.plancherelTerm {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f₁ f₂ : K → ℂ) : ℂ :=
  (Module.finrank ℂ ρ.carrier : ℂ) *
    LinearMap.trace ℂ ρ.carrier
      (((ρ.repFourierCoeff f₁).comp
        (ContinuousLinearMap.adjoint (ρ.repFourierCoeff f₂)) : ρ.carrier →L[ℂ] ρ.carrier) :
          ρ.carrier →ₗ[ℂ] ρ.carrier)

def IrrFinDimRep.plancherelSingleTerm {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f : K → ℂ) : ℂ :=
  (Module.finrank ℂ ρ.carrier : ℂ) *
    LinearMap.trace ℂ ρ.carrier
      ((ρ.repFourierCoeff f : ρ.carrier →L[ℂ] ρ.carrier) : ρ.carrier →ₗ[ℂ] ρ.carrier)

end PlancherelCompact
end
