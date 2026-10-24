/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

open scoped ZeroAtInfty
open Filter Topology

noncomputable section

namespace TestFunctions

variable (n : ℕ)

/-- A continuous, complex-valued function on `ℝⁿ` that vanishes at infinity, is `C¹`,
and whose first-order partial derivatives also vanish at infinity. -/
structure ContDiffZeroAtInfty extends
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  contDiff_one : ContDiff ℝ 1 ⇑toZeroAtInftyContinuousMap
  partialDeriv_zero_at_infty (j : Fin n) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (⇑toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1))
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

section RestrictionOfFunctionals

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {U : Type*} [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Pullback of continuous linear functionals along a continuous linear map
`ι : V →L[𝕜] U`: sends a dual element on `U` to its restriction along `ι`. -/
def restrictDual (ι : V →L[𝕜] U) : (U →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜) :=
  (compL 𝕜 V U 𝕜).flip ι

/-- The `C^k` sup-norm of a function `f : ℝⁿ → ℂ`: sum of sup norms of all partial
derivatives up to order `k`. -/
def ckNorm (n : ℕ) : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → ℝ
  | 0, f => ⨆ x, ‖f x‖
  | k + 1, f =>
    ckNorm n k f +
      Finset.sum Finset.univ fun j : Fin n =>
        ckNorm n k fun x => fderiv ℝ f x (EuclideanSpace.single j 1)

/-- The space of `C^k` functions on `ℝⁿ` vanishing at infinity together with all of
their iterated derivatives up to order `k`. -/
structure ContDiffZeroAtInftyN (n : ℕ) (k : ℕ) extends
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  contDiff_k : ContDiff ℝ k ⇑toZeroAtInftyContinuousMap
  iteratedFDeriv_zero_at_infty (m : ℕ) (hm : m ≤ k) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ m (⇑toZeroAtInftyContinuousMap) x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

variable {n}

/-- The `C^k`-norm of an element of `ContDiffZeroAtInftyN n k`. -/
def ContDiffZeroAtInftyN.normCk {k : ℕ} (u : ContDiffZeroAtInftyN n k) : ℝ :=
  ckNorm n k ⇑u.toZeroAtInftyContinuousMap

section WeightedSpaces

variable (n : ℕ)

/-- The Japanese bracket `⟨x⟩ := √(1 + ‖x‖²)`, a smooth weight comparable to `‖x‖`
at infinity used to define weighted function spaces. -/
def japaneseBracket (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (1 + ‖x‖ ^ 2)

/-- The Japanese bracket `⟨x⟩` is strictly positive. -/
theorem japaneseBracket_pos (x : EuclideanSpace ℝ (Fin n)) :
    0 < japaneseBracket n x := by
  unfold japaneseBracket
  apply Real.sqrt_pos_of_pos
  positivity

/-- Weighted `C^k`-functions on `ℝⁿ` vanishing at infinity: an element is represented
by a witness `v ∈ C^k` whose ratio against `⟨x⟩^{-l}` lies in the original space. -/
structure WeightedContDiffZeroAtInfty (n : ℕ) (k : ℕ) (l : ℕ) where
  witnessV : ContDiffZeroAtInftyN n k

/-- Underlying function `⟨x⟩^{-l} v(x)` for a weighted `C^k` element with witness `v`. -/
def WeightedContDiffZeroAtInfty.toFun {k l : ℕ}
    (u : WeightedContDiffZeroAtInfty n k l) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (↑(japaneseBracket n x ^ l))⁻¹ * u.witnessV.toZeroAtInftyContinuousMap x

end WeightedSpaces

section SchwartzSpace

variable (n : ℕ)

/-- The Schwartz space described as functions on `ℝⁿ` lying in every weighted
`C^k`-space with weight `⟨x⟩^{-l}` (Melrose Prop 7.3 characterisation). -/
structure SchwartzTestFunctionSpace where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  mem_weightedSpace (k l : ℕ) : ∃ w : WeightedContDiffZeroAtInfty n k l,
    ∀ x, toFun x = WeightedContDiffZeroAtInfty.toFun n w x

/-- Standard Schwartz space `𝓢(ℝⁿ, ℂ)` abbreviation. -/
abbrev schwartzSpace (n : ℕ) := SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ

namespace SchwartzTestFunctionSpace

variable {n : ℕ}

/-- `SchwartzTestFunctionSpace n` coerces to functions `ℝⁿ → ℂ`. -/
instance instFunLike : FunLike (SchwartzTestFunctionSpace n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
