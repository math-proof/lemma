/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneErgodic
import Def.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


theorem mem_traceBoundaryConnectionEvent
    {m : ℕ} {x : Site d} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ traceBoundaryConnectionEvent m x ↔ connBdry d m ω x := by
  simp only [traceBoundaryConnectionEvent, Set.mem_iUnion,
    Set.Finite.mem_toFinset, boxConnectionEvent, mem_withinConnEvent]
  constructor
  · rintro ⟨z, hzbdry, hx, hz, hconn⟩
    exact ⟨hx, z, hz, hzbdry, hconn⟩
  · rintro ⟨hx, z, hz, hzbdry, hconn⟩
    exact ⟨z, hzbdry, hx, hz, hconn⟩

theorem isClopen_traceBoundaryConnectionEvent (m : ℕ) (x : Site d) :
    IsClopen (traceBoundaryConnectionEvent m x) := by
  unfold traceBoundaryConnectionEvent
  exact isClopen_biUnion_finset fun z _ => isClopen_boxConnectionEvent m x z


end StatMech.FrontierB
