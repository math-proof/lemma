/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Def.v1.Atlas.IntroductionToFunctionalAnalysis.code.LpSpaces

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

open MeasureTheory

namespace LpSpaces

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {E : Type*} [NormedAddCommGroup E]

/-- $L^p(μ; E)$ is a normed additive commutative group for $1 ≤ p ≤ ∞$, with norm
$\|\cdot\|_p$. This is part of the statement that $L^p(E)$ is a normed vector space. -/
instance Lp_instNormedAddCommGroup {p : ENNReal} [Fact (1 ≤ p)] :
    NormedAddCommGroup (Lp E p μ) :=
  MeasureTheory.Lp.instNormedAddCommGroup

/-- $L^p(μ; E)$ is a normed vector space over $𝕜$ for $1 ≤ p ≤ ∞$. Together with the
additive group instance, this gives the statement that $L^p(E)$ is a normed vector space
under $\|\cdot\|_p$. -/
instance Lp_instNormedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {p : ENNReal} [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (Lp E p μ) :=
  MeasureTheory.Lp.instNormedSpace

end LpSpaces
end
