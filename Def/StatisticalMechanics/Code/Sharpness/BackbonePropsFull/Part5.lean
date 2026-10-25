/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part3
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def shb_backboneNum (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (ω : G.Path x y) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    if Sharpness.sources G (ofEdgeFun G m) = {x, y}
        ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then
      weight G β J (ofEdgeFun G m) else 0


noncomputable def shb_rho (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (ω : G.Path x y) : ℝ :=
  shb_backboneNum G β J x y ω / currentSum G β J ∅


end Sharpness
end StatMech
