/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
import Instance.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_dartEdgeSet {L n : ℕ}
    (d : Fin n → ons_Dart L) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  Finset.univ.image (fun k => ons_portEdge L (d k))

end StatMech.Onsager
