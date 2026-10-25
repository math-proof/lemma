/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part15
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos
    {c : Real} (hc : 2 < c) {N n : Nat} (hn : 0 < n)
    (p : Fin n → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hp.physicalCoordinateBetheEigenrelation hc p hphase


theorem sixVertexHalfFilledBetheRoots_physicalEigenrelation
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexCoordinateBetheEigenrelation
      (N := sixVertexFourWidth 0 k) c
      (sixVertexHalfFilledBetheRoots hc k) := by
  exact SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos
    hc (by omega) (sixVertexHalfFilledBetheRoots hc k)
    (sixVertexHalfFilledBetheRoots_is_multiplicativeSolution hc k)
    (sixVertexHalfFilledBetheRoots_phase_ne_one hc k)


end
end StatMech.FrontierD
