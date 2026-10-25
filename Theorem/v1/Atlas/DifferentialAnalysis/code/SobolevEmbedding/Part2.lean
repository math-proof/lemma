/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part4
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

open scoped SchwartzMap

namespace SchwartzRepresentation

variable {n : ℕ}

section SchwartzLpEmbedding

open MeasureTheory

/-- Every Schwartz derivative `∂^α φ` belongs to `L^2`. -/
theorem schwartzDerivMemLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemLp ((iterSchwartzDeriv α φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      EuclideanSpace ℝ (Fin n) → ℂ) 2 volume :=
  (iterSchwartzDeriv α φ).memLp 2

end SchwartzLpEmbedding
end SchwartzRepresentation
end
