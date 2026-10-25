/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part4
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem highTempInput_symmDiff_subset {S : Finset V} {o z : V}
    {p : HighTempSwitchInput (V := V)} (hp : p.Valid G S o z) :
    p.F ∆ p.H ⊆ G.edgeFinset := by
  intro e he
  rw [Finset.mem_symmDiff] at he
  rcases he with ⟨heF, _⟩ | ⟨heH, _⟩
  · exact hp.1 heF
  · exact (mem_highTempInternalEdges G S e).mp (hp.2.1 heH) |>.1


theorem highTempInput_symmDiff_sources {S : Finset V} {o z : V}
    {p : HighTempSwitchInput (V := V)} (hp : p.Valid G S o z) :
    HasOddBoundary (p.F ∆ p.H) (sourcePair o z) := by
  have h := hasOddBoundary_symmDiff hp.2.2.1 hp.2.2.2
  convert h using 1
  ext v
  simp only [Finset.mem_symmDiff, Finset.notMem_empty,
    not_false_eq_true, and_true, false_and, or_false]


end Sharpness
end StatMech
