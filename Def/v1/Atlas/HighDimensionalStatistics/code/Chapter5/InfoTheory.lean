module
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L2Space
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part5
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Convex.Jensen
open MeasureTheory InformationTheory Real


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/InfoTheory.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace InfoTheory

/-- Total variation distance between probability measures `P₀` and `P₁` on a measurable space,
defined as the supremum of `|P₀ S - P₁ S|` over measurable sets `S`. (Definition 5.4.) -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ : Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧ x = |(P₀ S).toReal - (P₁ S).toReal|}

/-- Real-valued version of the Kullback–Leibler divergence `klDiv P Q`, obtained by
taking `toReal` of the `ENNReal`-valued divergence. -/
noncomputable def klDiv_real {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  (klDiv P Q).toReal

/-- Bhattacharyya coefficient `BC(P, Q) = ∫ √(dP/dQ) dQ` between two measures. -/
noncomputable def bhattacharyyaCoeff {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  ∫ ω, Real.sqrt (P.rnDeriv Q ω).toReal ∂Q

/-- Uniform mixture measure `(1/M) ∑ⱼ Pⱼ` of a finite family of probability measures. -/
noncomputable def mixtureMeasure {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin M → Measure Ω) : Measure Ω :=
  (1 / (M : ENNReal)) • Finset.sum Finset.univ (fun j => P j)

/-- Squared Euclidean distance between two vectors `θ₁, θ₂ ∈ ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- `isMinIdx f n` holds when `n < M` and `f ⟨n, _⟩` is a minimum of `f` over `Fin M`. -/
def isMinIdx {M : ℕ} (f : Fin M → ℝ) (n : ℕ) : Prop :=
  ∃ h : n < M, ∀ k : Fin M, f ⟨n, h⟩ ≤ f k

end InfoTheory
end
