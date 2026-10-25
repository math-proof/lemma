/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part4
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def hexagonalFaceCenterOffset (white : Bool) : Complex :=
  if white then -(1 / 3 : Real) - (1 / 3 : Real) * Complex.I
  else (1 / 3 : Real) + (1 / 3 : Real) * Complex.I

end StatMech.FK.PeriodicPlanar
