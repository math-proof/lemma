module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part3
open scoped BigOperators
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularTorusIsingPartitionSequence
    (J1 J2 J3 : Real) (n : Nat) : Real := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  exact StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
    (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0)

end StatMech.FrontierA
