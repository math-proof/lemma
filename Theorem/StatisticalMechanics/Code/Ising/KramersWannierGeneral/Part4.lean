/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Def.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section K4Recovery

@[simp] theorem k4CompEquiv_apply (e : Sym2 (Fin 4)) : k4CompEquiv e = k4Comp e := rfl

@[simp] theorem k4CompEquiv_symm_apply (e : Sym2 (Fin 4)) : k4CompEquiv.symm e = k4Comp e := rfl


theorem mem_K4_edgeFinset_iff (e : Sym2 (Fin 4)) :
    e ∈ (K4).edgeFinset ↔ ¬ e.IsDiag := by
  rw [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.ind with
  | _ x y => rw [SimpleGraph.mem_edgeSet]; simp [K4, SimpleGraph.top_adj, Sym2.mk_isDiag_iff]


theorem k4Comp_not_diag (e : Sym2 (Fin 4)) (he : ¬ e.IsDiag) : ¬ (k4Comp e).IsDiag := by
  revert e; decide

set_option maxRecDepth 10000 in


theorem k4Comp_cut_to_even :
    ∀ δ ∈ cutSpaceB (K4), IsEvenSubgraph (δ.image k4Comp) := by decide

set_option maxRecDepth 10000 in


theorem k4Comp_even_to_cut :
    ∀ F ∈ evenSubgraphsB (K4), (F.image k4Comp) ∈ cutSpaceB (K4) := by decide


end K4Recovery
end Ising
end StatMech
