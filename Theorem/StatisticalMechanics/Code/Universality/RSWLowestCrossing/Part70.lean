/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part69
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightSafeTraceReachability_of_commonSafeConnectivity {n : ℤ}
    (hn : 0 < n) (hcommon : RlcRightCommonSafeConnectivity n) :
    RlcRightSafeTraceReachability n := by
  classical
  intro gamma delta
  have finish_from_common : ∀ u : ↑(rlc_rightCommonSupport gamma delta),
      ∃ y : rightSide 0 (2 * n) (-n) n,
        (y : Site 2) ∈ rlc_upperHalf ∧
        (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
        (rlc_rightSafeTraceGraph gamma delta).Reachable u.1
          ⟨y, rightSide_subset y.2⟩ := by
    intro u
    have hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
        (rlc_pathVertices delta.1) := by
      intro hdisj
      have huBoth : u.1 ∈ gamma.1.2.2.1.support.toFinset ∧
          u.1 ∈ delta.1.2.2.1.support.toFinset := by
        exact Finset.mem_inter.mp (by
          simpa [rlc_rightCommonSupport] using u.2)
      have huGamma : (u.1 : Site 2) ∈ rlc_pathVertices gamma.1 := by
        simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u.1, by simpa using huBoth.1, rfl⟩
      have huDelta : (u.1 : Site 2) ∈ rlc_pathVertices delta.1 := by
        simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u.1, by simpa using huBoth.2, rfl⟩
      exact (Finset.disjoint_left.mp hdisj) huGamma huDelta
    rcases rlc_exists_safe_right_endpoint hn gamma delta with hgamma | hdelta
    · obtain ⟨v, hv⟩ := rlc_last_common_reaches_safe_gamma_endpoint
        gamma delta hinter hgamma
      exact ⟨gamma.1.2.1, gamma.2.2, hgamma,
        (hcommon gamma delta u v).trans hv⟩
    · obtain ⟨v, hv⟩ := rlc_last_common_reaches_safe_delta_endpoint
        gamma delta hinter hdelta
      have hvMem : v.1 ∈ rlc_rightCommonSupport gamma delta := by
        simpa [rlc_rightCommonSupport, Finset.inter_comm] using v.2
      let v' : ↑(rlc_rightCommonSupport gamma delta) := ⟨v.1, hvMem⟩
      exact ⟨delta.1.2.1, delta.2.2, hdelta,
        (hcommon gamma delta u v').trans (by simpa [v'] using hv)⟩
  obtain ⟨x, hxHalf, hxUnion, hxSafe⟩ :=
    rlc_exists_safe_left_trace_anchor hn gamma delta
  let xs : rect 0 (2 * n) (-n) n := ⟨x, leftSide_subset x.2⟩
  rcases Finset.mem_union.mp hxUnion with hxGamma | hxDelta
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hxGamma
    obtain ⟨xg, hxg, hxgEq⟩ := hxGamma
    have hxgSub : xg = xs := by
      apply Subtype.ext
      exact hxgEq
    subst xg
    rcases rlc_safe_vertex_reaches_endpoint_or_common
        gamma delta hxg hxSafe with hEnd | hSwitch
    · have hEndSafe := rlc_rightSafeTraceGraph_reachable_dest_safe
        gamma delta hxSafe hEnd
      exact ⟨x, gamma.1.2.1, hxHalf, gamma.2.2,
        hxSafe, hEndSafe, hEnd⟩
    · obtain ⟨u, huGamma, huDelta, hxu⟩ := hSwitch
      simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        at huGamma huDelta
      obtain ⟨ug, hug, hugEq⟩ := huGamma
      obtain ⟨ud, hud, hudEq⟩ := huDelta
      have hugSub : ug = u := by apply Subtype.ext; exact hugEq
      have hudSub : ud = u := by apply Subtype.ext; exact hudEq
      subst ug
      subst ud
      have huMem : u ∈ rlc_rightCommonSupport gamma delta := by
        simp [rlc_rightCommonSupport, hug, hud]
      let us : ↑(rlc_rightCommonSupport gamma delta) := ⟨u, huMem⟩
      obtain ⟨y, hyHalf, hySafe, huy⟩ := finish_from_common us
      exact ⟨x, y, hxHalf, hyHalf, hxSafe, hySafe,
        hxu.trans (by simpa [us] using huy)⟩
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hxDelta
    obtain ⟨xd, hxd, hxdEq⟩ := hxDelta
    have hxdSub : xd = xs := by
      apply Subtype.ext
      exact hxdEq
    subst xd
    rcases rlc_safe_vertex_reaches_endpoint_or_common
        delta gamma hxd
          (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hxSafe) with
      hEnd | hSwitch
    · have hEnd' : (rlc_rightSafeTraceGraph gamma delta).Reachable xs
          ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
        simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
          Finset.union_comm, Set.union_comm] using hEnd
      have hEndSafe := rlc_rightSafeTraceGraph_reachable_dest_safe
        gamma delta hxSafe hEnd'
      exact ⟨x, delta.1.2.1, hxHalf, delta.2.2,
        hxSafe, hEndSafe, hEnd'⟩
    · obtain ⟨u, huDelta, huGamma, hxu⟩ := hSwitch
      have hxu' : (rlc_rightSafeTraceGraph gamma delta).Reachable xs u := by
        simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
          Finset.union_comm, Set.union_comm] using hxu
      simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        at huGamma huDelta
      obtain ⟨ug, hug, hugEq⟩ := huGamma
      obtain ⟨ud, hud, hudEq⟩ := huDelta
      have hugSub : ug = u := by apply Subtype.ext; exact hugEq
      have hudSub : ud = u := by apply Subtype.ext; exact hudEq
      subst ug
      subst ud
      have huMem : u ∈ rlc_rightCommonSupport gamma delta := by
        simp [rlc_rightCommonSupport, hug, hud]
      let us : ↑(rlc_rightCommonSupport gamma delta) := ⟨u, huMem⟩
      obtain ⟨y, hyHalf, hySafe, huy⟩ := finish_from_common us
      exact ⟨x, y, hxHalf, hyHalf, hxSafe, hySafe,
        hxu'.trans (by simpa [us] using huy)⟩


end Universality
end StatMech
