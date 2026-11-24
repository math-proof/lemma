module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_turnpreserveengine.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def jc_windowTurn (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ :=
  umEar_windowTurn K e a b


end Walls
end StatMech
