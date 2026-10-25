/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (hphase : forall j, sixVertexBethePhase (p j) ≠ 1)
    (hexpand : SixVertexPhysicalWordExpansion (N := N) c p) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  unfold SixVertexCoordinateBetheEigenrelation
  funext x
  rw [hexpand x, hp.cyclicWordEigenvalue_sector hc p x hphase]
  rfl

end
end StatMech.FrontierD
