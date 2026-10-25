/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def isingDeltaPairSum (β : ℝ) (J : Sym2 V → ℝ)
    (o x y g : V) : ℝ :=
  gatedSourcePairSum G β J (({o, g} : Finset V) ∆ {x, y}) ∅
    (fun m => CurrentConnected G m o x ∧ CurrentConnected G m y g ∧
      ¬ CurrentConnected G m o g)


noncomputable def isingDeltaLowerMass (β : ℝ) (J : Sym2 V → ℝ)
    (o x y g : V) : ℝ :=
  ∑ S : Finset V,
    if o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S then
      expectationJ G β (couplingIn J S) {o, x} *
        gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m g = S)
    else 0


noncomputable def isingDeltaSelfLowerMass (β : ℝ) (J : Sym2 V → ℝ)
    (o y g : V) : ℝ :=
  ∑ S : Finset V,
    if o ∈ S ∧ y ∉ S ∧ g ∉ S then
      gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m g = S)
    else 0


end Sharpness
end StatMech
