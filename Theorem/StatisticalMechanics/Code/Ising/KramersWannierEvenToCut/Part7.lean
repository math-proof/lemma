/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part7
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


section ClosedWalk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


theorem even_to_cut_of_closedWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
  refine even_to_cut_of_cycleParity hG ψ hsymm ?_
  intro F hF
  obtain ⟨ι, _hιdec, s, w, W, hcov, hdisj⟩ := hdecomp F hF
  
  have hsingle : SingleDualCycleParity Gp ψ
      (fun C => ∃ (z : V) (Wz : Gd.Walk z z), C = Wz.edges.toFinset) := by
    rintro C ⟨z, Wz, rfl⟩
    exact hlink Wz
  exact cycleParityCompatible_of_decomposition ψ hsingle s
    (fun i => (W i).edges.toFinset) hcov hdisj (fun i _ => ⟨w i, W i, rfl⟩)


end ClosedWalk
end Reduction
end Ising
end StatMech
