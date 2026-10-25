/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem exists_odd_closed_walk [Nonempty V] (hG : G.Preconnected)
    (q : CycleCompleteConstraint G) :
    ∃ (x : V) (p : G.Walk x x), walkParity G q.1 p = true := by
  have hnot : ¬ EvenOnCycles G q.1 := by
    intro heven
    exact q.2.2 ((evenOnCycles_iff_mem_cutSpace hG q.2.1).mp heven)
  simp only [EvenOnCycles, not_forall] at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨p, hp⟩ := hx
  refine ⟨x, p, ?_⟩
  cases hpar : walkParity G q.1 p <;> simp_all

end
end StatMech.FrontierA
