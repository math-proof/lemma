/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDual
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


noncomputable def torusCellDualCutGraph (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    torusCellPrimalOfDualEdge L s(f, g) ∉ G.edgeSet
  symm := by
    constructor
    rintro f g ⟨hfg, hwall⟩
    refine ⟨hfg.symm, ?_⟩
    simpa [Sym2.eq_swap] using hwall
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

end StatMech.BeffaraDC
