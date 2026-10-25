/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def torusPlanarPrimalHom (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    openSubgraph 2 (torusPlanarPullback L omega) →g
      FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega) where
  toFun := torusReduceSite L
  map_rel' := by
    intro x y hxy
    rw [FK.openSub_adj]
    refine ⟨torusReduceSite_adj L hxy.1, ?_⟩
    simpa [torusPlanarPullback] using hxy.2


end StatMech.BeffaraDC
