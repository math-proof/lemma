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
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice (card_components_bot card_components_eq_one_of_connected)

open StatMech.Onsager


def torusDualCutGraph (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    ¬ G.Adj (torusQuarterTurn L f) (torusQuarterTurn L g)
  symm := by
    constructor
    rintro f g ⟨hfg, hwall⟩
    exact ⟨hfg.symm, fun h => hwall h.symm⟩
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

end StatMech.BeffaraDC
