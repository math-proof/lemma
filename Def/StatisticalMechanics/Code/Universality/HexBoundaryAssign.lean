/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Structure.StatisticalMechanics.Code.Universality.HexBoundaryAssign


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexRegionCls (R : HexRegion) (z : ℂ) : Fin 5 :=
  if z = R.start then 0
  else if z.re = 0 then 1
  else if z.re = R.width then 4
  else if Real.sqrt 3 * z.im = R.slant + z.re then 2
  else if Real.sqrt 3 * z.im = -(R.slant + z.re) then 3
  else 0


end StatMech.Universality
