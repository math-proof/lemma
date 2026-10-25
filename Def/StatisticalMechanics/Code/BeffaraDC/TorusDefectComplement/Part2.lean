/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality.Part3
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusConfigOfGraph (L : ℕ)
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := by
  classical
  exact fun e => decide (e ∈ K.edgeSet)


end StatMech.BeffaraDC
