/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part6
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sourcelessCurrentFiniteMarginal_eq_localParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one)) =
      (PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le)).bind
        (finiteParityPMF S beta hbeta) := by
  rw [sourcelessCurrentFiniteMarginal_eq_parity_bind G beta hbeta S]
  rw [PMF.bind_map]
  congr 1
  funext H
  rw [parityCurrentPMF_map_restrictCurrent G beta hbeta H S]
  rfl

end Ambient
end StatMech.FrontierB
