module
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
public import Def.StatisticalMechanics.Code.FK.TriangularOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

@[simp] theorem triangularTransBoxIncl_val {R N : Nat} {x : Site 2}
    (hsub : triangularTransBox R x ⊆ box 2 N)
    (y : TriangularTransBoxVertex R x) :
    (triangularTransBoxIncl hsub y : Site 2) = y.1 := rfl

theorem triangularTransBoxIncl_injective {R N : Nat} {x : Site 2}
    (hsub : triangularTransBox R x ⊆ box 2 N) :
    Function.Injective (triangularTransBoxIncl hsub) := by
  intro y z hyz
  apply Subtype.ext
  exact congrArg (fun w : TriangularBoxVertex N => (w : Site 2)) hyz


end
end StatMech.FK.PeriodicPlanar
