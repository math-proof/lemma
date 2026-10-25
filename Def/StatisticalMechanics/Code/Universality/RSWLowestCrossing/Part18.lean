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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part17
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_leftShiftHom (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 (translateConfig (rlc_leftShift n) omega)
        (rect 0 (2 * n) (-n) n) →g
      openSubgraphInduce 2 omega (rect (-2 * n) 0 (-n) n) where
  toFun := fun x => ⟨(x : Site 2) + rlc_leftShift n, by
    have := (cti_mem_rect_translate 0 (2 * n) (-n) n (rlc_leftShift n) x).mp x.2
    simpa using this⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    exact (cti_isOpenEdge_translate (rlc_leftShift n) omega x y).mp hxy

noncomputable def rlc_leftShiftHomInv (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (rect (-2 * n) 0 (-n) n) →g
      openSubgraphInduce 2 (translateConfig (rlc_leftShift n) omega)
        (rect 0 (2 * n) (-n) n) where
  toFun := fun x => ⟨(x : Site 2) - rlc_leftShift n, by
    rw [cti_mem_rect_translate 0 (2 * n) (-n) n (rlc_leftShift n)]
    simpa using x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    have key := (cti_isOpenEdge_translate (rlc_leftShift n) omega
      ((x : Site 2) - rlc_leftShift n) ((y : Site 2) - rlc_leftShift n)).2
    simp only [sub_add_cancel] at key
    exact key hxy

end Universality
end StatMech
