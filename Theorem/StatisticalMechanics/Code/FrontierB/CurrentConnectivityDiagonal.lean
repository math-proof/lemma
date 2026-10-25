/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation.Part2
import Def.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice

variable {d : ℕ}


theorem currentPairTraceBoxGate_mono
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    Monotone (fun n => currentPairTraceBoxGate Q n x y) := by
  intro m n hmn p hp
  exact ⟨hp.1, boxConnectionEvent_mono x y hmn hp.2⟩

theorem iUnion_currentPairTraceBoxGate
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    (⋃ n, currentPairTraceBoxGate Q n x y) =
      currentPairTraceConnectionGate Q x y := by
  ext p
  simp only [Set.mem_iUnion, currentPairTraceBoxGate,
    currentPairTraceConnectionGate, Set.mem_preimage, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hQ, hn⟩
    exact ⟨hQ, (mem_iUnion_boxConnectionEvent_iff_connected
      (superposedCurrentTrace p) x y).mp (Set.mem_iUnion.mpr ⟨n, hn⟩)⟩
  · rintro ⟨hQ, hconn⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
      ((mem_iUnion_boxConnectionEvent_iff_connected
        (superposedCurrentTrace p) x y).mpr hconn)
    exact ⟨n, hQ, hn⟩

theorem isClopen_currentPairTraceBoxGate
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (n : ℕ) (x y : Site d) :
    IsClopen (currentPairTraceBoxGate Q n x y) :=
  (hQ.inter (isClopen_boxConnectionEvent n x y)).preimage
    continuous_superposedCurrentTrace


end StatMech.FrontierB
