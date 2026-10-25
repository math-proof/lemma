/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality.Part3
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torus_openSub_configOfGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    FK.openSub (onsTorusGraph L) (torusConfigOfGraph L K) = K := by
  classical
  ext x y
  simp only [FK.openSub_adj, torusConfigOfGraph, decide_eq_true_eq,
    SimpleGraph.mem_edgeSet]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hK h, h⟩


theorem torusGeometricDefect_add_dualCutGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    torusGeometricDefect L K +
      torusGeometricDefect L (torusDualCutGraph L K) = 2 := by
  let ω := torusConfigOfGraph L K
  have hopen : FK.openSub (onsTorusGraph L) ω = K :=
    torus_openSub_configOfGraph L K hK
  have hdual := torus_openSub_dualConfig L ω
  rw [hopen] at hdual
  simpa only [hopen, hdual] using torusGeometricDefect_add_dual L ω


theorem torusDefectClassified_of_nonnegative (L : ℕ) [Fact (2 < L)]
    (hnonneg : ∀ K : SimpleGraph (ZMod L × ZMod L), K ≤ onsTorusGraph L →
      0 ≤ torusGeometricDefect L K) :
    TorusDefectClassified L := by
  intro K hK
  have h0 := hnonneg K hK
  have hdual0 := hnonneg (torusDualCutGraph L K) (torusDualCutGraph_le L K)
  have hsum := torusGeometricDefect_add_dualCutGraph L K hK
  omega

end StatMech.BeffaraDC
