/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Structure.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
@[expose] public section

open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- Treat a Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpace n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpace.toFun⟩

end SobolevEmbedding
end
