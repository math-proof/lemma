/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def inhomogeneousDeletedCoupling
    (J : Sym2 V → ℝ) (F : Finset (Sym2 V)) : Sym2 V → ℝ :=
  fun e => if e ∈ F then 0 else J e

noncomputable def weightedEdgeSpinSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (s : ConfigSpace V) : ℝ :=
  ∑ e ∈ F, beta * J e * bond s e

end StatMech.FrontierB
