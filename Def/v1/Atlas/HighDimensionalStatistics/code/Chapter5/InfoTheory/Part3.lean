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
public import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part2
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

/-- Centering map sending `true ↦ 1/2` and `false ↦ -1/2`, used to turn Boolean variables
into centered `±1/2`-valued random variables. -/
noncomputable def boolCenter (b : Bool) : ℝ := if b then (1 : ℝ) / 2 else -(1 : ℝ) / 2

/-- The "XOR pairing" self-equivalence on `(Fin d → Bool) × (Fin d → Bool)`, sending
`(a, b)` to `(a, a ^^ b)`. Used to reduce pair-counting arguments to single-string counts. -/
def pairXorEquiv (d : ℕ) :
    (Fin d → Bool) × (Fin d → Bool) ≃ (Fin d → Bool) × (Fin d → Bool) where
  toFun p := (p.1, fun i => p.1 i ^^ p.2 i)
  invFun q := (q.1, fun i => q.1 i ^^ q.2 i)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- The `ℓ⁰`-norm of a Boolean vector: the number of coordinates equal to `true`. -/
def l0norm_bool {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card

end InfoTheory
end
