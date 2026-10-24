/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SchurLemma
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import sympy.atlas.v1.Atlas.LieGroups.code.IsotypicPeterWeyl
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace

noncomputable section

open MeasureTheory ContinuousRep
open scoped ComplexConjugate

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]

def matrixCoefficientOfEnd
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] [CompleteSpace W]
    (ρ : ContinuousRep K W) (A : W →L[ℂ] W) : K → ℂ :=
  fun g => (LinearMap.trace ℂ W) (A.comp (ρ.toMonoidHom g)).toLinearMap
