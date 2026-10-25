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
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part2
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- Sobolev embedding into `C_0^k`: the iterated derivative `D^j f` vanishes at
infinity (cocompactly) when `f` has `H^m` regularity above the Sobolev threshold. -/
structure SobolevSpaceWeak (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

end SobolevEmbedding
end
