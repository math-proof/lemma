/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open Real Set Topology


noncomputable section

namespace CM8

/-- Opaque predicate: $\Omega \subset \mathbb{R}^n$ is a (bounded) Lipschitz
domain. Left abstract here since regularity details of the boundary are not
used in these formal statements. -/
opaque IsLipschitzDomain : {n : ℕ} → Set (Fin n → ℝ) → Prop

/-- The Euclidean norm on $\mathbb{R}^n$ written as
$\|x\| = \sqrt{\sum_i x_i^2}$. -/
def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The fundamental solution of the Laplacian in $\mathbb{R}^3$:
$\Phi(x) = -\dfrac{1}{4 \pi |x|}$, away from the origin. -/
def Phi3 (x : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * euclidNorm x)

/-- The Laplacian of $f : \mathbb{R}^n \to \mathbb{R}$ at $x$, defined in terms
of Fréchet derivatives applied to coordinate unit vectors:
$\Delta f(x) = \sum_{i = 1}^{n} \partial_i (\partial_i f)(x)$. -/
noncomputable def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)


section HarmonicProofHelpers

open Finset

/-- The squared Euclidean norm $\|y\|^2 = \sum_j y_j^2$ on $\mathbb{R}^3$. -/
def normSq (y : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, y j ^ 2

/-- The continuous linear map representing the Fréchet derivative of
$y \mapsto \sum_j y_j^2$ at $x$: it acts as $v \mapsto 2 \sum_j x_j v_j$. -/
def normSq_CLM (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 3, (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) j


/-- The sum of squares of the coordinates of $x$ other than the $i$-th:
$\sum_{j \ne i} x_j^2$. Used to reduce a multivariable derivative to a
one-dimensional computation. -/
def restSq (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j ∈ Finset.univ.filter (· ≠ i), x j ^ 2

end HarmonicProofHelpers
end CM8
end
