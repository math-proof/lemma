/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part6


namespace StatMech.FrontierA

def TriangularTorusZeroHomologyWinding (L : Nat) [Fact (2 < L)] : Prop :=
  ∀ {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
        p.edges.toFinset = 0 →
      ∑ k, triangularIntStep
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0


end StatMech.FrontierA
