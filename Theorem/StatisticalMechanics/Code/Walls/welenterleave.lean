/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean -/

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
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wel_enterLeaveAlt (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (c₀ : ℤ) (N : ℕ)
    (hbase : wis_indSeq z Vc c₀ 0 = 0) :
    wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) :=
  wos_indNonzeroDiffs_alternates z Vc c₀ N hbase


theorem wel_enterLeaveHead (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (c₀ : ℤ) (N : ℕ)
    (hbase : wis_indSeq z Vc c₀ 0 = 0)
    (hne : wis_nonzeroDiffs (wis_indSeq z Vc c₀) N ≠ []) :
    (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).headI = 1 :=
  wos_nonzeroDiffs_head_one (wis_indSeq z Vc c₀)
    (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N hne


end Lattice
end StatMech
