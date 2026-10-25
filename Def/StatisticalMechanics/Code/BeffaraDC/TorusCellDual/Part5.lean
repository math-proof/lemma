/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part4
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


noncomputable def torusCellFaceCount (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℕ :=
  Nat.card (torusCellDualCutGraph L G).ConnectedComponent


noncomputable def torusCellDefect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℤ :=
  (G.edgeSet.ncard : ℤ) - Nat.card (ZMod L × ZMod L) +
    Nat.card G.ConnectedComponent + 1 - torusCellFaceCount L G


end StatMech.BeffaraDC
