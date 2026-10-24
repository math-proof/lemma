/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM4/WeakMaximumPrinciple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Basic

open Set

noncomputable section

namespace WeakMaximumPrinciple

/-- The open spacetime cylinder $Q_T = (0,T) \times (a,b) \subseteq \mathbb{R}^2$,
the spatial-temporal domain on which the heat equation is posed. -/
def SpacetimeCylinder (T a b : ℝ) : Set (ℝ × ℝ) :=
  Ioo 0 T ×ˢ Ioo a b

/-- The closed spacetime cylinder $\overline{Q_T} = [0,T] \times [a,b]$,
the closure of the spacetime cylinder where the solution is required to be continuous. -/
def ClosedCylinder (T a b : ℝ) : Set (ℝ × ℝ) :=
  Icc 0 T ×ˢ Icc a b

/-- The parabolic boundary $\partial_p Q_T = (\{0\} \times [a,b]) \cup ((0,T] \times \{a,b\})$,
i.e. the bottom of the cylinder together with its lateral sides (but not the top). -/
def ParabolicBoundary (T a b : ℝ) : Set (ℝ × ℝ) :=
  ({0} ×ˢ Icc a b) ∪ (Ioc 0 T ×ˢ {a, b})

/-- The heat operator $L_D u = u_t - D \, u_{xx}$ acting on a function $u : \mathbb{R}^2 \to \mathbb{R}$
at a point $p = (t, x)$, with diffusion constant $D$. -/
def HeatOp (u : ℝ × ℝ → ℝ) (D : ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun t => u (t, p.2)) p.1 1 -
    D * fderiv ℝ (fun x => fderiv ℝ (fun x' => u (p.1, x')) x 1) p.2 1
