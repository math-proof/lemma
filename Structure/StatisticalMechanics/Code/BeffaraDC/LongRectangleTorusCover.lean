/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part4
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


structure BdcTorusWindingToThinCover
    (L alpha n : ℕ) [Fact (2 < L)]
    (W : Set (TorusAmbientConfig L)) : Prop where
  toThin : ∀ omega, omega ∈ W → bdcTorusThinCrossing L alpha n omega


end StatMech.BeffaraDC
