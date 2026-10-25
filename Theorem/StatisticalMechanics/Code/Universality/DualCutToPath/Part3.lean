/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Def.StatisticalMechanics.Code.Universality.DualCutToPath.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcp_cutReachable_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) : dcp_CutReachable ω n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, _⟩ := hcut
  exact ⟨p₀, hp₀, q₀, hq₀, c.reachable⟩


theorem dcp_dualOpen_reachable_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) :
    ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n)
      (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n),
      (openSubgraph 2 (dualConfig ω)).Reachable p₀ q₀ := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, _⟩ := hcut
  exact ⟨p₀, hp₀, q₀, hq₀, dcw_dualBarrier_reachable_open ω n c.reachable⟩


theorem dcp_dualBarrierGraph_support_rot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Adj p q) :
    p ∈ rect (-n) 0 0 n := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  have hvbox : v ∈ rect 0 n 0 n := hvw.1.1
  have hwbox : w ∈ rect 0 n 0 n := hvw.2.1
  rw [mem_rect] at hvbox hwbox
  have hrot : ∀ x : Site 2, x ∈ rect 0 n 0 n → rot90Fun x ∈ rect (-n) 0 0 n := by
    intro x hx
    rw [mem_rect] at hx
    rw [mem_rect, rot90Fun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rcases hpq with ⟨hp, _⟩ | ⟨hp, _⟩
  · rw [hp]; exact hrot v hvbox
  · rw [hp]; exact hrot w hwbox


theorem dcp_rot90_leftSide (n : ℤ) {x : Site 2} (hx : x ∈ leftSide 0 n 0 n) :
    rot90Fun x ∈ bottomSide (-n) 0 0 n := by
  obtain ⟨hbox, h0⟩ := hx
  rw [mem_rect] at hbox
  have hsnd : (rot90Fun x) 1 = x 0 := by rw [rot90Fun]; rfl
  refine ⟨?_, ?_⟩
  · rw [mem_rect, rot90Fun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [hsnd, h0]


theorem dcp_rot90_rightSide (n : ℤ) {x : Site 2} (hx : x ∈ rightSide 0 n 0 n) :
    rot90Fun x ∈ topSide (-n) 0 0 n := by
  obtain ⟨hbox, hn⟩ := hx
  rw [mem_rect] at hbox
  have hsnd : (rot90Fun x) 1 = x 0 := by rw [rot90Fun]; rfl
  refine ⟨?_, ?_⟩
  · rw [mem_rect, rot90Fun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [hsnd, hn]


end Universality
end StatMech
