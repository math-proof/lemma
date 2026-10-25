/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


noncomputable def torusCellDualOfPrimalEdge (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) : Sym2 (ZMod L × ZMod L) :=
  if he : e ∈ (onsTorusGraph L).edgeFinset then
    (torusCellCrossing L ⟨e, he⟩ : TorusAmbientEdge L)
  else e

end StatMech.BeffaraDC
