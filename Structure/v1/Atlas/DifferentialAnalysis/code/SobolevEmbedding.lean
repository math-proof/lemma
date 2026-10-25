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
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- A (strong) Sobolev space `H^m` on `ℝ^n`: smooth functions `u : ℝ^n → ℂ` of class
`C^m` such that each iterated Fréchet derivative `D^j u` (for `j ≤ m`) is square
integrable with respect to Lebesgue measure. -/
structure SobolevSpace (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  contDiff_toFun : ContDiff ℝ (m : ℕ∞) toFun
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

end SobolevEmbedding
end
