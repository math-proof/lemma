/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
import Theorem.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
import Def.StatisticalMechanics.Code.Walls.woborientbridge.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wob_columnSortedEqJumps_iff_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    wob_ColumnSortedEqJumps z Vc ↔ wel_OrientationConsistent z Vc := Iff.rfl


theorem wob_orientationConsistent_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc) :
    wel_OrientationConsistent z Vc :=
  (wob_columnSortedEqJumps_iff_orientationConsistent z Vc).mp h


theorem wob_signsAlternate_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc) :
    wos_SignsAlternateInColumnOrder z Vc :=
  wel_signsAlternate_of_orientationConsistent z Vc
    (wob_orientationConsistent_of_columnSortedEqJumps z Vc h)


theorem wob_columnAlternates_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc) :
    wna_ColumnAlternates z Vc :=
  wel_columnAlternates_of_orientationConsistent z Vc
    (wob_orientationConsistent_of_columnSortedEqJumps z Vc h)


theorem wob_signedCross_pm_one_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc)
    (hodd : ¬ Even (jec_rayCount z Vc)) :
    wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 :=
  wel_signedCross_pm_one z Vc (wob_orientationConsistent_of_columnSortedEqJumps z Vc h) hodd


end Lattice
end StatMech
