/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part5
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


def torusCellOldObstructionConfig3 :
    ConfigSpace (Sym2 (ZMod 3 × ZMod 3)) := fun e => decide (e ∈ ({
      s(((0, 0) : ZMod 3 × ZMod 3), ((1, 0) : ZMod 3 × ZMod 3)),
      s(((0, 1) : ZMod 3 × ZMod 3), ((1, 1) : ZMod 3 × ZMod 3)),
      s(((0, 2) : ZMod 3 × ZMod 3), ((1, 2) : ZMod 3 × ZMod 3)),
      s(((1, 0) : ZMod 3 × ZMod 3), ((2, 0) : ZMod 3 × ZMod 3)),
      s(((1, 0) : ZMod 3 × ZMod 3), ((1, 1) : ZMod 3 × ZMod 3)),
      s(((1, 1) : ZMod 3 × ZMod 3), ((2, 1) : ZMod 3 × ZMod 3)),
      s(((1, 1) : ZMod 3 × ZMod 3), ((1, 2) : ZMod 3 × ZMod 3)),
      s(((1, 2) : ZMod 3 × ZMod 3), ((2, 2) : ZMod 3 × ZMod 3))} :
        Finset (Sym2 (ZMod 3 × ZMod 3))))

end StatMech.BeffaraDC
