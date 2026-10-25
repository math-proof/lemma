/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
import Def.StatisticalMechanics.Code.FK.TriHexBrickWiredCofinal.Part4
open Filter Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.OSSS

noncomputable section

theorem triangularBufferedBoxActiveEvent_increasing (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    IsIncreasing (triangularBufferedBoxActiveEvent k m hkm A) := by
  intro rho eta hrho hmem
  exact hA (monotone_triangularBoxBufferedActiveRestrict k m hkm hrho) hmem


end
end StatMech.FK.PeriodicPlanar
