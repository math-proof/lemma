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
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part8
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section RegionSide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


omit [Fintype V] [DecidableRel Gd.Adj] in


theorem dualWalkBoundsRegion_isSideColouring
    (ψ : Sym2 V ≃ Sym2 V) (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    DualWalkHasSideColouring Gp Gd ψ := by
  intro w W
  obtain ⟨S, hS⟩ := hreg W
  exact ⟨S, fun h => hS h⟩

omit [Fintype V] [DecidableRel Gd.Adj] in


theorem closedDualWalkParity_of_boundsRegion
    (ψ : Sym2 V ≃ Sym2 V) (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    ClosedDualWalkParity Gp Gd ψ := by
  intro w W
  obtain ⟨S, hS⟩ := hreg W
  
  
  intro x p
  rw [walkParity_eq_xor_of_isCoboundary S (fun h => hS h) p]
  cases S x <;> rfl


theorem even_to_cut_of_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp :=
  even_to_cut_of_sideColouring hG ψ hsymm hdecomp
    (dualWalkBoundsRegion_isSideColouring ψ hreg)


end RegionSide
end Ising
end StatMech
