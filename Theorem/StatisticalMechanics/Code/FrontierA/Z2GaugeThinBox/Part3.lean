/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

theorem thinBoxDualGraph_isTree (n : ℕ) :
    (thinBoxDualGraph n).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · simpa [thinBoxDualGraph] using SimpleGraph.pathGraph_connected n
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Nat.card_eq_fintype_card]
    have hcard := Fintype.card_congr (thinBoxDualEdge n)
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      congrArg (fun k => k + 1) hcard.symm


theorem thinBox_isClosed (n : ℕ) (A : Finset (thinBoxPlaquette n)) :
    IsClosedPlaquetteSet (thinBoxIncidence n) A := by
  intro e
  exact Fin.elim0 e


end
end StatMech.FrontierA
