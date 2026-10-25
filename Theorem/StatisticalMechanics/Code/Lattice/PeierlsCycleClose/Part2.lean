/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
import Def.StatisticalMechanics.Code.Lattice.PeierlsCycleClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem pcy_fig8_eq : wpc_fig8 = pcy_fig8_A.append pcy_fig8_B := rfl


theorem pcy_fig8_A_not_nil : ¬ pcy_fig8_A.Nil := by
  rw [pcy_fig8_A, SimpleGraph.Walk.nil_append_iff]
  rintro ⟨h1, _⟩
  have h0 := congrFun h1.eq 0; simp at h0


theorem pcy_fig8_B_not_nil : ¬ pcy_fig8_B.Nil := by
  rw [pcy_fig8_B, SimpleGraph.Walk.nil_append_iff]
  rintro ⟨h1, _⟩
  have h0 := congrFun h1.eq 0; simp at h0


theorem pcy_fig8_not_cycle : ¬ wpc_fig8.IsCycle := by
  intro hcyc
  have htail := hcyc.support_nodup
  rw [pcy_fig8_eq, SimpleGraph.Walk.tail_support_append, List.nodup_append] at htail
  obtain ⟨_, _, hdisj⟩ := htail
  have hA : (![2, 2] : Site 2) ∈ pcy_fig8_A.support.tail :=
    SimpleGraph.Walk.end_mem_tail_support pcy_fig8_A_not_nil
  have hB : (![2, 2] : Site 2) ∈ pcy_fig8_B.support.tail :=
    SimpleGraph.Walk.end_mem_tail_support pcy_fig8_B_not_nil
  exact hdisj _ hA _ hB rfl


end Lattice
end StatMech
