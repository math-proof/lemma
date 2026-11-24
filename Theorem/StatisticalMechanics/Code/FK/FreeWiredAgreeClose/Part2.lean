module
public import Theorem.StatisticalMechanics.Code.FK.FreeIVErgodicClose.Part2
public import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
public import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
public import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
public import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
public import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKLimitsErgodicUncond
public import Def.StatisticalMechanics.Code.FK.FreeWiredAgreeClose
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem fwa_badTilt_countable (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    (fwa_badTilt d N).Countable := by
  obtain ⟨eb, heb⟩ := Finset.card_pos.mp (ecz_box_edge_pos d hd hN)
  exact ecz_fk_uniqueness hd N eb heb


end FK
end StatMech
