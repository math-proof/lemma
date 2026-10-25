/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part7
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


noncomputable def edgeCrossing_of_closedWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
    (hdecomp : EvenSubgraphWalkDecomp Gd)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    EdgeCrossing Gp Gd where
  ψ := ψ
  edge_mem := hedge
  cut_to_even := hfwd
  even_to_cut := even_to_cut_of_closedWalkParity hG ψ hsymm hdecomp hlink


end ClosedWalk
end Reduction
end Ising
end StatMech
