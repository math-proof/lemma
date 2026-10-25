/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


theorem isOpenEdge_symm {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : IsOpenEdge d ω x y) : IsOpenEdge d ω y x := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj.symm, ?_⟩
  rwa [Sym2.eq_swap]

theorem isOpenEdge_irrefl {ω : ConfigSpace (Sym2 (Site d))} (x : Site d) :
    ¬ IsOpenEdge d ω x x := fun h => h.1.ne rfl

theorem isOpenEdge_imp_adj {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : IsOpenEdge d ω x y) : (hypercubicLattice d).Adj x y := h.1


end Lattice
end StatMech
