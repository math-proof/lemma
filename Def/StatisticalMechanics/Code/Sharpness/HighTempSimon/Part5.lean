/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def highTempSwitch (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) (p : HighTempSwitchInput (V := V))
    (hp : p.Valid G S o z) : HighTempSwitchOutput (V := V) := by
  let K := p.F ∆ p.H
  let d := highTempFirstExit G K
    (highTempInput_symmDiff_subset G hp)
    (highTempInput_symmDiff_sources G hp) S ho hz
  exact
    { x := d.x
      y := d.y
      A := p.H ∆ d.Q
      B := (p.F ∆ d.Q).erase s(d.x, d.y) }

end Sharpness
end StatMech
