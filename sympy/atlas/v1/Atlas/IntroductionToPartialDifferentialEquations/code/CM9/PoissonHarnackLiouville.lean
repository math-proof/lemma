/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenExistence
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties

open Set Real MeasureTheory Filter Topology

noncomputable section

namespace PoissonHarnack

/-- The open Euclidean ball $B_R(c) = \{x : \|x - c\| < R\}$ in $\mathbb{R}^n$, using
the Euclidean norm `CM8.euclidNorm`. -/
def euclidBall {n : ℕ} (c : Fin n → ℝ) (R : ℝ) : Set (Fin n → ℝ) :=
  {x | CM8.euclidNorm (x - c) < R}

/-- The Kelvin reflection of $x$ across the sphere $\partial B_R(p) \subset \mathbb{R}^3$:
$x^* = p + \frac{R^2}{|x-p|^2}(x - p)$. This maps the interior of the ball to its exterior
and is used to construct the Green function for a ball. -/
def kelvinReflection (p : Fin 3 → ℝ) (R : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => p i + R ^ 2 * (x i - p i) / CM8.euclidNorm (x - p) ^ 2

/-- The Green function for the ball $B_R(p) \subset \mathbb{R}^3$ defined via the
fundamental solution and its image under Kelvin reflection:
$G(x, y) = \Phi_3(x - y) - \frac{R}{|x-p|}\,\Phi_3(x^* - y)$. -/
def greenBall (R : ℝ) (p x y : Fin 3 → ℝ) : ℝ :=
  CM8.Phi3 (x - y) - (R / CM8.euclidNorm (x - p)) * CM8.Phi3 (kelvinReflection p R x - y)

/-- The explicit closed-form expression of `greenBall` for $x \neq p$:
$G(x,y) = -\frac{1}{4\pi|x-y|} + \frac{1}{4\pi}\cdot\frac{R}{|x-p|\,\bigl|\frac{R^2}{|x-p|^2}(x-p)-(y-p)\bigr|}$. -/
noncomputable def greenBallFormula (R : ℝ) (p x y : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * CM8.euclidNorm (x - y)) +
    R / (4 * Real.pi * CM8.euclidNorm (x - p) *
         CM8.euclidNorm (fun i => R^2 / CM8.euclidNorm (x - p)^2 * (x i - p i) - (y i - p i)))

/-- The value of the Green function for the ball at the center $p$:
$G(p, y) = -\frac{1}{4\pi|y-p|} + \frac{1}{4\pi R}$. -/
noncomputable def greenBallFormula_at_center (R : ℝ) (p y : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * CM8.euclidNorm (y - p)) + 1 / (4 * Real.pi * R)

section BoundaryVanishHelpers

private def normSq (x : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, x i ^ 2

/-- The standard inner product of two vectors in $\mathbb{R}^3$: $\langle a, b \rangle = \sum_i a_i b_i$. -/
def innerProd3 (a b : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, a i * b i

/-- The Poisson kernel for the ball $B_R(p) \subset \mathbb{R}^3$:
$P(x, y) = \frac{R^2 - |x-p|^2}{4\pi R\,|x-y|^3}$. This is the negative outward normal
derivative of the Green function on the boundary. -/
def poissonKernel (R : ℝ) (p x y : Fin 3 → ℝ) : ℝ :=
  (R ^ 2 - CM8.euclidNorm (x - p) ^ 2) / (4 * Real.pi * R * CM8.euclidNorm (x - y) ^ 3)

section EuclidBallTopology

/-- Squared Euclidean norm in $\mathbb{R}^3$ as a function: $y \mapsto \sum_j y_j^2$. -/
def normSq3' (y : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, y j ^ 2

/-- Fréchet derivative of `normSq3'` at $x$ packaged as a continuous linear map:
$v \mapsto \sum_j 2 x_j v_j = 2\langle x, v\rangle$. -/
def normSq3_CLM' (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 3, (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) j

/-- The natural identification of a tuple $v : \mathrm{Fin}\,n \to \mathbb{R}$ with an
element of the $\ell^2$ norm space `PiLp 2 (fun _ => ℝ)`. -/
def toPiLp {n : ℕ} (v : Fin n → ℝ) : PiLp 2 (fun _ : Fin n => ℝ) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm v
