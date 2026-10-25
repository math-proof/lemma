/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


@[simp] theorem torusCellDualCutGraph_adj (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (f g : ZMod L × ZMod L) :
    (torusCellDualCutGraph L G).Adj f g ↔
      (onsTorusGraph L).Adj f g ∧
        torusCellPrimalOfDualEdge L s(f, g) ∉ G.edgeSet := Iff.rfl


end StatMech.BeffaraDC
