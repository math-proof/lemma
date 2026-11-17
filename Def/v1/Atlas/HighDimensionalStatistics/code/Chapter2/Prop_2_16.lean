/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option maxHeartbeats 800000

open Matrix Finset BigOperators MeasureTheory ProbabilityTheory Real ENNReal


/-- The Rademacher distribution on `ℝ`: a fair mixture of point masses at `+1` and `-1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  (2 : ENNReal)⁻¹ • Measure.dirac (1 : ℝ) + (2 : ENNReal)⁻¹ • Measure.dirac (-1 : ℝ)

/-- An `n × d` random matrix `X` is *i.i.d. Rademacher* if its entries are jointly
independent, each marginal equals the Rademacher distribution under the pushforward of `μ`,
and the coordinate maps are measurable. -/
def IsIIDRademacherMatrix {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ} (X : Ω → Matrix (Fin n) (Fin d) ℝ) (μ : Measure Ω) : Prop :=

  @iIndepFun Ω (Fin n × Fin d) _ (fun _ => ℝ) (fun _ => inferInstance)
    (fun p : Fin n × Fin d => fun ω => X ω p.1 p.2) μ ∧

  (∀ (i : Fin n) (j : Fin d), Measure.map (fun ω => X ω i j) μ = rademacherMeasure) ∧

  (∀ (i : Fin n) (j : Fin d), Measurable (fun ω => X ω i j))

/-- The incoherence assumption `INC(k)`: `|XᵀX / n − I_d|_∞ ≤ 1 / (14 k)`, i.e. the
empirical Gram matrix is close to the identity entrywise. -/
def AssumptionINC {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (k : ℕ) : Prop :=
  ∀ i j : Fin d,
    |((Xᵀ * X) i j : ℝ) / (n : ℝ) - if i = j then 1 else 0| ≤ 1 / (14 * (k : ℝ))

/-- The fair coin distribution on `Fin 2`, used to model a single Rademacher bit. -/
noncomputable def coinMeasure : Measure (Fin 2) :=
  (2 : ENNReal)⁻¹ • Measure.dirac (0 : Fin 2) + (2 : ENNReal)⁻¹ • Measure.dirac (1 : Fin 2)

