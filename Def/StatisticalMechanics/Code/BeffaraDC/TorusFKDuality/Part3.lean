module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part3
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Onsager


def TorusDefectClassified (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ K : SimpleGraph (ZMod L × ZMod L), K ≤ onsTorusGraph L →
    torusGeometricDefect L K = 0 ∨ torusGeometricDefect L K = 1 ∨
      torusGeometricDefect L K = 2


end StatMech.BeffaraDC
