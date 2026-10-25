/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.SharpThreshold
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality


def kcd_localOneArm (x : Site 2) (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  (ConfigSpace.shift (Multiplicative.ofAdd (-x))) ⁻¹' crossingEvent 2 n


end StatMech.TwoDim
