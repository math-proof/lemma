/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc41split
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.RandomCurrent (sources connK degK compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


section AbstractPi

variable {E : Type*} [Fintype E] [DecidableEq E] {γ : E → Type*}
  [∀ e, Fintype (γ e)] [∀ e, DecidableEq (γ e)]


noncomputable def gc41_pairSigmaEquivPi :
    (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e)) ≃ (Π e : E, Finset (γ e) × Finset (γ e)) where
  toFun p := fun e => (sigmaFinsetEquivPi p.1 e, sigmaFinsetEquivPi p.2 e)
  invFun f := (sigmaFinsetEquivPi.symm (fun e => (f e).1), sigmaFinsetEquivPi.symm (fun e => (f e).2))
  left_inv p := by
    obtain ⟨S₁, S₂⟩ := p
    simp only [Prod.mk.injEq]
    constructor <;> · rw [← Equiv.eq_symm_apply]; rfl
  right_inv f := by funext e; simp only [Equiv.apply_symm_apply]


end AbstractPi
end StatMech.Walls
