/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Def.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decPortChainPath_isPath
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decPortChainPath L site a b).IsPath :=
  (Classical.choose_spec (ons_exists_decPortChainPath L site a b)).1

@[simp] theorem ons_decPortChainPath_edges_toFinset
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decPortChainPath L site a b).edges.toFinset =
      ons_decChainPathEdges site a b :=
  (Classical.choose_spec (ons_exists_decPortChainPath L site a b)).2

theorem ons_dartRev_fst_eq_step
    (L : ℕ) (d : ons_Dart L) :
    (ons_dartRev L d).1 = ons_dirStep L d.2 d.1 := by
  rfl


end StatMech.Onsager
