/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularTorusNormalizedSectorSequence
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2) (n : Nat) : Complex := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  exact
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
      Complex) *
      triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b


noncomputable def triangularTorusNormalizedSectorMaxSequence
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) : Real :=
  arfSectorNormMax fun a b =>
    triangularTorusNormalizedSectorSequence J1 J2 J3 rho a b n


noncomputable def triangularTorusRealEdgeWeight
    (L : Nat) (t1 t2 t3 : Real) :
    Sym2 (ZMod L × ZMod L) -> Real := fun edge =>
  if squareTorusHorizontalEdge L edge then t1
  else if triangularTorusVerticalEdge L edge then t2
  else t3

end StatMech.FrontierA
