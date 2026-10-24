/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace TheoryOfProbability3

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- A *decreasing filtration* on `(Ω, m0)` is a sequence of sub-σ-algebras
`ℱ n ⊆ m0` that is antitone in `n` (i.e. `ℱ 0 ⊇ ℱ 1 ⊇ ℱ 2 ⊇ ⋯`). This is the
natural index structure for backwards martingales, where conditioning
σ-algebras shrink as `n → ∞`. -/
structure DecreasingFiltration (Ω : Type*) (m0 : MeasurableSpace Ω) where
  seq : ℕ → MeasurableSpace Ω
  antitone' : Antitone seq
  le' : ∀ n, seq n ≤ m0

attribute [coe] DecreasingFiltration.seq

/-- Allow a `DecreasingFiltration` to be applied as a function `ℕ → MeasurableSpace Ω`
via its underlying sequence `seq`. -/
instance : CoeFun (DecreasingFiltration Ω m0) (fun _ => ℕ → MeasurableSpace Ω) where
  coe := DecreasingFiltration.seq

/-- The *tail σ-algebra* of a decreasing filtration `ℱ`, defined as the
intersection `⨅ n, ℱ n`. This is the σ-algebra of events that lie in every
`ℱ n`, i.e. the limit as the filtration shrinks. -/
@[reducible]
def DecreasingFiltration.tailAlgebra (ℱ : DecreasingFiltration Ω m0) :
    MeasurableSpace Ω :=
  ⨅ n, ℱ.seq n

/-- A *backwards martingale* with respect to a decreasing filtration `ℱ` and
measure `μ` is a process `M : ℕ → Ω → ℝ` such that `M 0` is integrable, each
`M n` is `ℱ n`-strongly measurable, and `M n = μ[M 0 | ℱ n]` `μ`-a.e.
Equivalently, `E(M n | ℱ n+1) = M n+1` for all `n` (with the filtration shrinking
as `n` grows). This corresponds to the setting of Durrett's backwards
martingale convergence theorem: `X_{-∞} = lim_{n → -∞} X_n` exists a.s. and in
`L¹`. -/
structure IsBackwardsMartingale (M : ℕ → Ω → ℝ) (ℱ : DecreasingFiltration Ω m0)
    (μ : Measure Ω) : Prop where
  integrable_zero : Integrable (M 0) μ
  adapted : ∀ n, StronglyMeasurable[ℱ n] (M n)
  condExp_ae_eq : ∀ n, M n =ᵐ[μ] μ[M 0 | ℱ n]
