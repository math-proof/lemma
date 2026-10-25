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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem torusReduceSite_mk (L : ℕ) (a b : ℤ) :
    torusReduceSite L ![a, b] = ((a : ZMod L), (b : ZMod L)) := by
  rfl


end StatMech.BeffaraDC
