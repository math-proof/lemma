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
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part13
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section UnconditionalCapstone

variable {V : Type} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


noncomputable def edgeCrossing_of_boundsRegion' [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    EdgeCrossing Gp Gd :=
  edgeCrossing_of_boundsRegion hG ψ hedge hsymm hfwd (evenSubgraphWalkDecomp_general Gd) hreg


end UnconditionalCapstone
end Ising
end StatMech
