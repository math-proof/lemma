/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


noncomputable def torusCellDualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := fun e =>
  if he : e ∈ (onsTorusGraph L).edgeFinset then
    !(ω (torusCellPrimalOfDualEdge L e))
  else false


end StatMech.BeffaraDC
