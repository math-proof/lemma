/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentFiniteMarginal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def nonnegativeSplitEdgeCurrent
    (S : Finset G.edgeFinset) :
    EdgeCurrent G ≃ ((↑S → ℕ) × ({e : G.edgeFinset // e ∉ S} → ℕ)) :=
  Equiv.piEquivPiSubtypeProd (fun e => e ∈ S) (fun _ => ℕ)

end StatMech.FrontierB
