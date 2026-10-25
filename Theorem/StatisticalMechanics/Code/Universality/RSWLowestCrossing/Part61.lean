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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part60
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightTraceGraph_reachable_of_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {z u v : rect 0 (2 * n) (-n) n}
    (hzGamma : z ∈ gamma.1.2.2.1.support)
    (hzDelta : z ∈ delta.1.2.2.1.support)
    (hu : u ∈ gamma.1.2.2.1.support)
    (hv : v ∈ delta.1.2.2.1.support) :
    (rlc_rightTraceGraph gamma delta).Reachable u v := by
  let pg := rlc_rightTraceGraph_walk_left gamma delta
  let pd := rlc_rightTraceGraph_walk_right gamma delta
  have huPg : u ∈ pg.support := by
    simpa only [pg, rlc_rightTraceGraph_walk_left,
      SimpleGraph.Walk.support_transfer] using hu
  have hzPg : z ∈ pg.support := by
    simpa only [pg, rlc_rightTraceGraph_walk_left,
      SimpleGraph.Walk.support_transfer] using hzGamma
  have hzPd : z ∈ pd.support := by
    simpa only [pd, rlc_rightTraceGraph_walk_right,
      SimpleGraph.Walk.support_transfer] using hzDelta
  have hvPd : v ∈ pd.support := by
    simpa only [pd, rlc_rightTraceGraph_walk_right,
      SimpleGraph.Walk.support_transfer] using hv
  have huz : (rlc_rightTraceGraph gamma delta).Reachable u z :=
    ⟨(pg.takeUntil u huPg).reverse.append (pg.takeUntil z hzPg)⟩
  have hzv : (rlc_rightTraceGraph gamma delta).Reachable z v :=
    ⟨(pd.takeUntil z hzPd).reverse.append (pd.takeUntil v hvPd)⟩
  exact huz.trans hzv


end Universality
end StatMech
