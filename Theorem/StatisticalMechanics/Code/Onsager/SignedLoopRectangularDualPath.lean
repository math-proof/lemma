/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part3
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

theorem ons_rectDualPathDefect_subset_edgeFinset
    {M N : Nat} (path : ons_RectDualPath M N) :
    ons_rectDualPathDefect path ⊆ (ons_rectDualGraph M N).edgeFinset := by
  intro edge hedge
  obtain ⟨⟨u, v⟩, huv⟩ := edge.exists_rep
  rw [← huv] at hedge ⊢
  rw [SimpleGraph.mem_edgeFinset]
  exact path.walk.adj_of_mem_edges
    (by simpa [ons_rectDualPathDefect] using hedge)


theorem ons_rectDualPathDefect_hasOddBoundary
    {M N : Nat} (path : ons_RectDualPath M N) :
    HasOddBoundary (ons_rectDualPathDefect path) {path.source, path.target} := by
  have hboundary := hasOddBoundary_path_edges path.walk path.isPath
  rw [sourcePair_eq_pair path.source_ne_target] at hboundary
  exact hboundary


end
end StatMech.Onsager
