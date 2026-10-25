/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decPortChainPath
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decGraph L).Walk (site, a) (site, b) :=
  Classical.choose (ons_exists_decPortChainPath L site a b)

end StatMech.Onsager
