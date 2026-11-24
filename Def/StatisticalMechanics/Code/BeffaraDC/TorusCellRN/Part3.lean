module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusAmbientDefect (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : ℤ :=
  torusCellDefect L
    (FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega))


end StatMech.BeffaraDC
