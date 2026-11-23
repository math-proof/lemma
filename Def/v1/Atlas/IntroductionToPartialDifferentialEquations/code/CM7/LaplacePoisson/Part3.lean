/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
public import Theorem.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson.Part3

@[expose] public section

open Real Set MeasureTheory Filter


noncomputable section

namespace LaplacePoisson

/-- $\Delta \Phi = \delta_x$ distributionally on `EuclideanSpace ℝ (Fin 3)`: for any
$C^2$ test function $\varphi$ with compact support,
$\int -1/(4\pi |y - x|)\,\Delta \varphi(y)\,dy = \varphi(x)$. -/
def kelvinImageE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  p + (R / ‖x - p‖) ^ 2 • (x - p)

/-- Key Kelvin-image identity: for $\sigma$ on the sphere $\partial B(p, R)$,
$\|x^* - \sigma\| = (R/\|x - p\|)\,\|x - \sigma\|$. This produces the boundary
cancellation of $G$ on $\partial B(p, R)$. -/
def greenBallFunctionE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if x = p then
    -1 / (4 * Real.pi * ‖y - p‖) + 1 / (4 * Real.pi * R)
  else
    -1 / (4 * Real.pi * ‖y - x‖) +
      (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖))

end LaplacePoisson
end
