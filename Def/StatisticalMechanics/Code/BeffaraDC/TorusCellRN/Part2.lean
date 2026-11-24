module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN
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


noncomputable def torusAmbientFKWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) : ℝ :=
  FK.fkWeight (onsTorusGraph L) p q (torusAmbientConfigExtend L omega)


end StatMech.BeffaraDC
