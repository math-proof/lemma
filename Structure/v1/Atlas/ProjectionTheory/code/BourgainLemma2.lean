/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainLemma2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.BourgainLemma2


namespace BourgainMultiscale

open Set MeasureTheory

/-- `AdmissibleBranching f t` packages the hypotheses on the branching profile $f : [0,1] \to
\mathbb{R}$: $f$ is monotone, $2$-Lipschitz, satisfies $f(0)=0$, $f(1)=t$, and the lower bound
$f(x) \geq t\cdot x$. -/
structure AdmissibleBranching (f : ℝ → ℝ) (t : ℝ) : Prop where
  monotone : MonotoneOn f (Icc 0 1)
  lipschitz : LipschitzOnWith 2 f (Icc 0 1)
  f_zero : f 0 = 0
  f_one : f 1 = t
  lower_bound : ∀ x ∈ Icc (0 : ℝ) 1, f x ≥ t * x


end BourgainMultiscale
