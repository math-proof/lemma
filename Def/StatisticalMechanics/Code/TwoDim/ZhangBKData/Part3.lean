/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part3
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


def zbd_sideHasInfinite {d : ℕ} (S : Set (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | ∃ x ∈ S, (cluster d omega x).Infinite}

end StatMech.TwoDim
