/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Abbrev.StatisticalMechanics.Code.BeffaraDC.TorusCellRN
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusCellDualAmbientConfig (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : TorusAmbientConfig L :=
  fun e => !(omega ((torusCellCrossing L).symm e))


noncomputable def torusCellDualAmbientConfigEquiv (L : ℕ) [Fact (2 < L)] :
    TorusAmbientConfig L ≃ TorusAmbientConfig L where
  toFun := torusCellDualAmbientConfig L
  invFun eta := fun e => !(eta (torusCellCrossing L e))
  left_inv omega := by
    funext e
    simp [torusCellDualAmbientConfig]
  right_inv eta := by
    funext e
    simp [torusCellDualAmbientConfig]


def torusAmbientConfigExtend (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := fun e =>
  if he : e ∈ (onsTorusGraph L).edgeFinset then omega ⟨e, he⟩ else false


def torusAmbientConfigRestrict (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    TorusAmbientConfig L := fun e => omega e.1

end StatMech.BeffaraDC
