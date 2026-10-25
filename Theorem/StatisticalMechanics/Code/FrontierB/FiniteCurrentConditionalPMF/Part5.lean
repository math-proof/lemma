/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part4
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem splitEdgeCurrent_fst (S : Finset G.edgeFinset)
    (m : EdgeCurrent G) :
    (splitEdgeCurrent G S m).1 = restrictCurrent S m := by
  funext e
  rfl

theorem restrictCurrent_splitEdgeCurrent_symm
    (S : Finset G.edgeFinset) (a : ↑S → ℕ)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    restrictCurrent S ((splitEdgeCurrent G S).symm (a, b)) = a := by
  funext e
  change (Equiv.piEquivPiSubtypeProd (fun x : G.edgeFinset => x ∈ S)
    (fun _ => ℕ)).symm (a, b) e.1 = a e
  rw [Equiv.piEquivPiSubtypeProd_symm_apply]
  simp [e.2]

end Ambient
end StatMech.FrontierB
