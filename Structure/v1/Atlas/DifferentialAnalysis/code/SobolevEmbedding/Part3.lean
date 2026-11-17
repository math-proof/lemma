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
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part3
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


public noncomputable section

namespace SobolevEmbedding

/-- **Sobolev embedding** (Melrose Cor. 10.3): if `k ≤ m` and `n < 2(m - k)`,
then every weak Sobolev function `u ∈ H^m` is (a.e. equal to) a `C^k` function
whose derivatives of order `≤ k` all vanish at infinity, i.e. `H^m ↪ C_0^k`. -/
structure SobolevInfty (n : ℕ) where
  mem_sobolev : ∀ m : ℕ, SobolevSpace n m
  consistent : ∀ m₁ m₂ : ℕ, (mem_sobolev m₁).toFun = (mem_sobolev m₂).toFun

end SobolevEmbedding
end
