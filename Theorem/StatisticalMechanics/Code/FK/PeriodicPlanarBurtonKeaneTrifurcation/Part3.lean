/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part3
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


theorem PeriodicGraph.fundamentalDomain_mem_orbitBox_zero
    (P : PeriodicGraph V) {u : V} (hu : u ∈ P.fundamentalDomain) :
    u ∈ P.orbitBox 0 := by
  rw [P.mem_orbitBox_iff]
  exact ⟨0, by simp, u, hu, by rw [P.shift_zero]; rfl⟩

theorem PeriodicGraph.neighbor_mem_orbitBox_add
    (P : PeriodicGraph V) {n : Nat} {x y : V}
    (hx : x ∈ P.orbitBox n) (hxy : P.graph.Adj x y) :
    y ∈ P.orbitBox (n + P.neighborOrbitRadius) := by
  rw [P.mem_orbitBox_iff] at hx ⊢
  obtain ⟨z, hz, u, hu, rfl⟩ := hx
  let y0 := P.shift (-z) y
  have hadj0 : P.graph.Adj u y0 := by
    have hm := (P.shift_adj (-z) (P.shift z u) y).2 hxy
    simpa [y0] using hm
  have hy0 : y0 ∈ P.orbitBox P.neighborOrbitRadius := by
    exact P.neighbor_mem_nextBufferedRadius 0
      (P.fundamentalDomain_mem_orbitBox_zero hu) hadj0
  rw [P.mem_orbitBox_iff] at hy0
  obtain ⟨w, hw, v, hv, hwv⟩ := hy0
  refine ⟨w + z, ?_, v, hv, ?_⟩
  · rw [mem_box] at hz hw ⊢
    intro i
    calc
      ((w + z) i).natAbs <= (w i).natAbs + (z i).natAbs :=
        Int.natAbs_add_le _ _
      _ <= P.neighborOrbitRadius + n := Nat.add_le_add (hw i) (hz i)
      _ = n + P.neighborOrbitRadius := Nat.add_comm _ _
  · have hshift : P.shift z y0 = y := by simp [y0]
    rw [← hshift, ← hwv]
    exact P.shift_add w z v

end StatMech.FK.PeriodicPlanar
