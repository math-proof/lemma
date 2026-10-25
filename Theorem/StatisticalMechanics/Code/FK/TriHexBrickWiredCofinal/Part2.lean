/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
import Def.StatisticalMechanics.Code.FK.TriHexBrickWiredCofinal.Part2
open Filter Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.OSSS

noncomputable section

theorem triangularBoxLiftEvent_increasing {n m : Nat} (hnm : n ≤ m)
    {A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)}
    (hA : IsIncreasing A) : IsIncreasing (triangularBoxLiftEvent hnm A) := by
  intro rho eta hrho hmem
  exact hA (monotone_triangularBoxActiveRestrictLE hnm hrho) hmem

theorem triHexFaceDualInnerEvent_lift {n m : Nat} (hnm : n ≤ m)
    (A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)) :
    triHexFaceDualInnerEvent m (triangularBoxLiftEvent hnm A) =
      triHexFaceDualInnerEvent n A := by
  ext omega
  change triangularBoxActiveRestrictLE hnm
      (triHexFaceDualInnerActive m omega) ∈ A ↔
    triHexFaceDualInnerActive n omega ∈ A
  rw [triHexFaceDualInnerActive_restrictLE]


end
end StatMech.FK.PeriodicPlanar
