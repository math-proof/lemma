/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisOrContactObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeAxisBridge.Part2
import Def.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff
    (t : ℤ) (e : Sym2 (Site 2)) :
    rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t) e = true ↔
      e = rlc_reflectedFailureAnchorEdge t := by
  have hpims : rlc_pimsEdgeEquiv (rlc_reflectedFailureAnchorEdge t) =
      s(![0, t], ![0, t + 1]) := by
    simpa [rlc_reflectedFailureAnchorEdge] using
      (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))
  rw [rlc_dualReflectConfig_eq_pims]
  simpa [rlc_singleClosedFailureAnchorConfig, hpims] using
    (rlc_pimsEdgeEquiv.apply_eq_iff_eq
      (x := e) (y := rlc_reflectedFailureAnchorEdge t))


theorem rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints
    (t : ℤ) {z : Site 2}
    (hreach : (openSubgraph 2
      (rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t))).Reachable
        ![-1, t + 1] z) :
    z = ![-1, t + 1] ∨ z = ![0, t + 1] := by
  obtain ⟨p⟩ := hreach
  have walk_stays {x y : Site 2}
      (q : (openSubgraph 2
        (rlc_dualReflectConfig
          (rlc_singleClosedFailureAnchorConfig t))).Walk x y)
      (hx : x = ![-1, t + 1] ∨ x = ![0, t + 1]) :
      y = ![-1, t + 1] ∨ y = ![0, t + 1] := by
    induction q with
    | nil => exact hx
    | @cons u v w huv q ih =>
        rw [openSubgraph_adj] at huv
        have heq :=
          (rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff
            t s(u, v)).mp huv.2
        have hv : v ∈ rlc_reflectedFailureAnchorEdge t := by
          rw [← heq]
          exact Sym2.mem_mk_right _ _
        rw [rlc_reflectedFailureAnchorEdge, Sym2.mem_iff] at hv
        exact ih hv
  exact walk_stays p (Or.inl rfl)


theorem rlc_singleClosedFailureAnchor_no_raw_extension (t : ℤ) :
    ¬ (openSubgraph 2
      (rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t))).Reachable
        ![-1, t + 1] ![1, t + 1] := by
  intro hreach
  rcases rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints
    t hreach with h | h <;> simp at h

end Universality
end StatMech
