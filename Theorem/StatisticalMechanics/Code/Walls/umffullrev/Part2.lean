/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanOrbitCycle.Part2
import Def.StatisticalMechanics.Code.Walls.umffullrev.Part2
open scoped BigOperators
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem umf_Ltromino_kingSaturated : npm_KingSaturated umf_Ltromino :=
  joc_Ltromino_kingSaturated


theorem umf_Ltromino_faceMultiplicityOne (a : {e : Dart // IsBoundaryDart umf_Ltromino e}) :
    usc_FaceMultiplicityOne umf_Ltromino a :=
  joc_Ltromino_faceMultiplicityOne a


end Lattice
end StatMech
