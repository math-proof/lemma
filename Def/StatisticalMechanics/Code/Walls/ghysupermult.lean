/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult
open Finset BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghy_zeta (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset (Sym2 V)) : ℝ :=
  ZJ (E \ S) J hf / ZJ E J hf * ∏ e ∈ S, Real.cosh (J e)


noncomputable def ghy_rho (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset (Sym2 V)) : ℝ :=
  ghy_zeta E J hf S * ∏ e ∈ S, Real.tanh (J e)


end StatMech.Walls
