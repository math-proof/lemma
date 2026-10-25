/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson.Part3
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
