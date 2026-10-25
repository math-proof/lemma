/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


theorem openSubgraph_mono_dim {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω') :
    openSubgraph d ω ≤ openSubgraph d ω' := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y)
  rw [hxy.2] at hle
  exact top_le_iff.mp hle


theorem connected_mono_dim {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω')
    {x y : Site d} (hxy : Connected d ω x y) : Connected d ω' x y :=
  hxy.mono (openSubgraph_mono_dim h)


theorem cluster_mono_dim {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω')
    (x : Site d) : cluster d ω x ⊆ cluster d ω' x :=
  fun _ hy => connected_mono_dim h hy


end Universality
end StatMech
