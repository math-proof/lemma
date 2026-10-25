/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusGeometricEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice (card_components_bot card_components_eq_one_of_connected)

open StatMech.Onsager


noncomputable def torusGeometricFaceCount (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℕ :=
  Nat.card (torusDualCutGraph L G).ConnectedComponent


noncomputable def torusGeometricDefect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℤ :=
  (G.edgeSet.ncard : ℤ) - Nat.card (ZMod L × ZMod L) +
    Nat.card G.ConnectedComponent + 1 - torusGeometricFaceCount L G


end StatMech.BeffaraDC
