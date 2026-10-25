/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part6
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def restrictParity (S : Finset G.edgeFinset) (H : Finset (Sym2 V)) :
    ↑S → Bool := fun e => decide (e.1.1 ∈ H)

end Ambient
end StatMech.FrontierB
