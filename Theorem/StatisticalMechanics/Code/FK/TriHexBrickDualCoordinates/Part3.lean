/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFiniteDualComparison
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part17
import Def.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates.Part3
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

theorem continuous_triHexFaceDualInnerActive (N : Nat) :
    Continuous (triHexFaceDualInnerActive N) := by
  apply continuous_pi
  intro a
  exact (continuous_of_discreteTopology :
    Continuous (fun b : Bool => !b)).comp
      (continuous_apply (triHexFullDualEdgeEquiv
        (Sym2.map Subtype.val a.1)))

theorem antitone_triHexFaceDualInnerActive (N : Nat) :
    Antitone (triHexFaceDualInnerActive N) := by
  intro omega eta home a
  unfold triHexFaceDualInnerActive
  have h := home (triHexFullDualEdgeEquiv
    (Sym2.map Subtype.val a.1))
  cases h1 : omega (triHexFullDualEdgeEquiv
      (Sym2.map Subtype.val a.1)) <;>
    cases h2 : eta (triHexFullDualEdgeEquiv
      (Sym2.map Subtype.val a.1)) <;>
    simp_all

end
end StatMech.FK.PeriodicPlanar
