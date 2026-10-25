/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheMonomial_eq_intMonomial {N n : Nat}
    (p : Fin n -> Real) (sigma : Equiv.Perm (Fin n))
    (x : SixVertexSector N n) :
    sixVertexBetheMonomial p sigma x =
      sixVertexBetheIntMonomial p sigma
        (sixVertexSectorIntCoordinates x) := by
  unfold sixVertexBetheMonomial sixVertexBetheIntMonomial
    sixVertexSectorIntCoordinates
  apply Finset.prod_congr rfl
  intro i _
  rw [zpow_natCast]


theorem sixVertexCoordinateBetheWave_eq_intWave {N n : Nat}
    (c : Real) (p : Fin n -> Real) (x : SixVertexSector N n) :
    sixVertexCoordinateBetheWave c p x =
      sixVertexCoordinateBetheIntWave c p
        (sixVertexSectorIntCoordinates x) := by
  unfold sixVertexCoordinateBetheWave sixVertexCoordinateBetheIntWave
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexBetheMonomial_eq_intMonomial]


theorem SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue_sector
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : SixVertexSector N (n + 1))
    (hphase : forall j, sixVertexBethePhase (p j) ≠ 1) :
    (∑ w : Finset (Fin (n + 1)),
      ∑ sigma, sixVertexBetheAmplitude c p sigma *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase (p j)) sigma w *
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase (p j)) sigma
          (sixVertexSectorIntCoordinates x) w) =
      sixVertexBetheEigenvalueCandidate c p *
        sixVertexCoordinateBetheWave c p x := by
  rw [sixVertexCoordinateBetheWave_eq_intWave]
  exact hp.cyclicWordEigenvalue hc p
    (sixVertexSectorIntCoordinates x) hphase


end
end StatMech.FrontierD
