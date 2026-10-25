/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentFiniteMarginal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
import Def.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentFiniteMarginal
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem restrictCurrent_nonnegativeSplitEdgeCurrent_symm
    (S : Finset G.edgeFinset) (a : ↑S → ℕ)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    restrictCurrent S
        ((nonnegativeSplitEdgeCurrent G S).symm (a, b)) = a := by
  funext e
  change (Equiv.piEquivPiSubtypeProd (fun x : G.edgeFinset => x ∈ S)
    (fun _ => ℕ)).symm (a, b) e.1 = a e
  rw [Equiv.piEquivPiSubtypeProd_symm_apply]
  simp [e.2]

end StatMech.FrontierB
