/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section SideColouring

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


omit [DecidableRel Gd.Adj] in


theorem closedDualWalkParity_of_sideColouring
    (ψ : Sym2 V ≃ Sym2 V) (hside : DualWalkHasSideColouring Gp Gd ψ) :
    ClosedDualWalkParity Gp Gd ψ := by
  intro w W
  obtain ⟨c, hc⟩ := hside W
  exact evenOnCycles_of_isCoboundary c (fun h => hc h)


theorem even_to_cut_of_sideColouring [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hside : DualWalkHasSideColouring Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp :=
  even_to_cut_of_closedWalkParity hG ψ hsymm hdecomp
    (closedDualWalkParity_of_sideColouring ψ hside)


end SideColouring
end Ising
end StatMech
