/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs


/-- The $N$-jet of the function $u$ at the point $x$: bundles $x$ together with
$\{\partial^{\alpha} u(x)\}_{|\alpha| \le N}$. -/
noncomputable def jetOf {n : ℕ} (N : ℕ) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    PDEJet n N where
  point := x
  derivatives := fun ⟨α, _hα⟩ => multiIndexDeriv α u x

