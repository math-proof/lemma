/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.Wave3D
set_option maxHeartbeats 3200000


noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- Predicate stating that $u : \mathbb{R} \times \mathbb{R}^3 \to \mathbb{R}$
is a $C^2$ solution of the $3$-dimensional wave equation
$-\partial_t^2 u + \Delta u = 0$. -/
structure IsWaveSolution3D (u : ℝ → E3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)
  wave_eq : ∀ t : ℝ, ∀ x : E3,
    fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' x) s 1) t 1 =
    ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (fun y' => u t y') y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1)

/-- Cauchy data for the $3$D wave equation: an initial position $f \in C^3(\mathbb{R}^3)$
and an initial velocity $g \in C^2(\mathbb{R}^3)$. -/
structure CauchyData3D where
  f : E3 → ℝ
  g : E3 → ℝ
  f_smooth : ContDiff ℝ 3 f
  g_smooth : ContDiff ℝ 2 g

end WaveEquation3D
end
