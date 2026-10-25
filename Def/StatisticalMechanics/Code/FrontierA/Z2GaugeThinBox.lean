/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

def thinBoxIncidence (n : ℕ) :
    thinBoxPlaquette n → Finset thinBoxGaugeEdge :=
  fun _ => ∅


def thinBoxPlaquetteEdge (n : ℕ) (i : thinBoxPlaquette n) :
    (thinBoxDualGraph n).edgeFinset :=
  ⟨s(i.castSucc, i.succ), by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.pathGraph_adj]
    left
    simp⟩

end
end StatMech.FrontierA
