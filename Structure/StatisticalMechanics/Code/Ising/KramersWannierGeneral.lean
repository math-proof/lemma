/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EdgeCrossing

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


structure EdgeCrossing where
  
  ψ : Sym2 V ≃ Sym2 V
  
  edge_mem : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset
  
  cut_to_even : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ)
  

  even_to_cut : ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp

end EdgeCrossing
end Ising
end StatMech
