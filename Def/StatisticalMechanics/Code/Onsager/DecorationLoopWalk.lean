/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk


namespace StatMech.Onsager

open Finset SimpleGraph

def ons_decGeometricStep (L : ℕ) (source target : ons_Dart L) : Prop :=
  target.1 = ons_dirStep L source.2 source.1

noncomputable def ons_decWalkEdgeCount
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : ons_DecEdge L →₀ ℕ := by
  classical
  exact Multiset.toFinsupp (p.edges : Multiset (ons_DecEdge L))

end StatMech.Onsager
