module
public import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
public import Def.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment
open Finset SimpleGraph Set MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcInsetLeftSourcePath (n : Int) :=
  RlcRestrictedCrossingPath (-2 * n) (-1) (-n) n rlc_lowerHalf rlc_strictUpperHalf

end
end StatMech.Universality
