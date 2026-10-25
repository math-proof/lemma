/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessOffCentre
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

noncomputable def hexagonalCenteredDenom
    (n : Nat) (q beta : Real) : Real :=
  4 * (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ j ∈ Finset.range n,
      hexagonalOuterCenteredConn n q beta x j) / (n : Real)

end StatMech.FK.PeriodicPlanar
