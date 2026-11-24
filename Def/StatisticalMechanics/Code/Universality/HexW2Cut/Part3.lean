module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraCut
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Cut.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


noncomputable def hexW2_cutWidth (h0 : ℤ) (ts : List ℤ) : ℕ :=
  ⌊hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)⌋₊


end StatMech.Universality
