/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part4
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def splitEdgeCurrent (S : Finset G.edgeFinset) :
    EdgeCurrent G ≃ ((↑S → ℕ) × ({e : G.edgeFinset // e ∉ S} → ℕ)) :=
  Equiv.piEquivPiSubtypeProd (fun e => e ∈ S) (fun _ => ℕ)

end Ambient
end StatMech.FrontierB
