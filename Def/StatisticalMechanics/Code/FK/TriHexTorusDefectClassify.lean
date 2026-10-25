/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

noncomputable def triHexTorusDualCutGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) : SimpleGraph (HexTorusVertex L) where
  Adj f g := (hexagonalTorusGraph L).Adj f g ∧
    triHexTorusPrimalOfDualEdge L s(f, g) ∉ K.edgeSet
  symm := by
    constructor
    rintro f g ⟨hfg, hclosed⟩
    refine ⟨hfg.symm, ?_⟩
    simpa [Sym2.eq_swap] using hclosed
  loopless := ⟨fun f h => (hexagonalTorusGraph L).irrefl h.1⟩

end PeriodicPlanar
end FK
end StatMech
