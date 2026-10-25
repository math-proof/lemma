/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part6
import Def.StatisticalMechanics.Code.Universality.GreenStubClose.Part4
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gst_fullWire_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {e : Sym2 (Site 2)}
    (h : e ∈ gst_fullWireSet n) : gst_fullWireConfig ω n e = true := by
  classical
  unfold gst_fullWireConfig; simp [h]


theorem gst_wire_reach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n) (k : ℕ)
    (hk : (k : ℤ) ≤ n + 1) :
    (openSubgraphInduce 2 (gst_fullWireConfig ω n) (rect (-n) 0 0 (n + 1))).Reachable
      ⟨![-n, 0], by rw [mem_rect]; simp; omega⟩
      ⟨![-n, (k : ℤ)], by rw [mem_rect]; simp; omega⟩ := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    have hmle : (m : ℤ) ≤ n + 1 := by push_cast at hk ⊢; omega
    have step : (openSubgraphInduce 2 (gst_fullWireConfig ω n) (rect (-n) 0 0 (n + 1))).Adj
        ⟨![-n, (m : ℤ)], by rw [mem_rect]; simp; omega⟩
        ⟨![-n, ((m : ℤ) + 1)], by rw [mem_rect]; simp; omega⟩ := by
      rw [openSubgraphInduce_adj, openSubgraph_adj]
      refine ⟨by rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp, ?_⟩
      apply gst_fullWire_open
      exact ⟨![-n, (m : ℤ)], ![-n, (m : ℤ) + 1], rfl, by rw [mem_rect]; simp; omega,
        by rw [mem_rect]; simp; omega, by simp, by simp⟩
    have hcast : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hrec := (ih hmle).trans step.reachable
    rw [show (⟨![-n, ((m + 1 : ℕ) : ℤ)], by rw [mem_rect]; simp; omega⟩ :
          (rect (-n) 0 0 (n + 1) : Set (Site 2))) =
          ⟨![-n, (m : ℤ) + 1], by rw [mem_rect]; simp; omega⟩ from by
      apply Subtype.ext; simp [hcast]]
    exact hrec


theorem gst_fullWire_trivial (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n) :
    VerticalCrossing (gst_fullWireConfig ω n) (-n) 0 0 (n + 1) := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (n + 1) - 0)
  have hbmem : (![-n, 0] : Site 2) ∈ bottomSide (-n) 0 0 (n + 1) := by
    refine ⟨?_, by simp⟩; rw [mem_rect]; simp; omega
  have hkeq : (k : ℤ) = n + 1 := by omega
  have hval1 : (![-n, (k : ℤ)] : Site 2) 1 = (k : ℤ) := by simp
  have hval0 : (![-n, (k : ℤ)] : Site 2) 0 = -n := by simp
  have htmem : (![-n, (k : ℤ)] : Site 2) ∈ topSide (-n) 0 0 (n + 1) := by
    refine ⟨?_, by rw [hval1]; omega⟩
    rw [mem_rect, hval0, hval1]; omega
  exact ⟨⟨![-n, 0], hbmem⟩, ⟨![-n, (k : ℤ)], htmem⟩, gst_wire_reach ω n hn k (by omega)⟩


end Universality
end StatMech
