/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Instance.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching
open scoped symmDiff


namespace StatMech.FrontierB

open Sharpness

open Finset MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

open scoped Classical in
theorem gatedSourcePairSum_switching_local
    (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    {u v : V} (huv : u ≠ v) (S : Finset (Sym2 V))
    (Q : (↑S → ℕ) → Prop) [DecidablePred Q] :
    gatedSourcePairSum G beta J (A ∆ ({u, v} : Finset V)) {u, v}
        (currentLocalPattern S Q) =
      gatedSourcePairSum G beta J A ∅
        (fun m => currentLocalPattern S Q m ∧ CurrentConnected G m u v) :=
  gatedSourcePairSum_switching G beta J A huv (currentLocalPattern S Q)

end StatMech.FrontierB
