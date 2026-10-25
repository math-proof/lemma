/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellComplement
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


noncomputable def torusCellCutDualGraph (L : ℕ) [Fact (2 < L)]
    (S : Set (ZMod L × ZMod L)) : SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    torusCellEdgeStraddles S (torusCellPrimalOfDualEdge L s(f, g))
  symm := by
    constructor
    rintro f g ⟨hfg, hcut⟩
    refine ⟨hfg.symm, ?_⟩
    simpa [Sym2.eq_swap] using hcut
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

end StatMech.BeffaraDC
