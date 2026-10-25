/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCoordinateBetheWave_oddFinCast_ne_zero
    {N n m : Nat} (h : n = m) (c : Real) (p : Fin n → Real)
    (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
        (fun i : Fin m => p (Fin.cast h.symm i)) ≠ 0 := by
  subst m
  simpa using hwave

theorem sixVertexSectorTopEigenvalue_oddFinCast
    {N n m : Nat} (h : n = m) (hn : n ≤ N) (hm : m ≤ N)
    (c value : Real)
    (hv : value = sixVertexSectorTopEigenvalue N n hn c) :
    value = sixVertexSectorTopEigenvalue N m hm c := by
  subst m
  simpa using hv

theorem sixVertexZeroPhaseBetheEigenvalueValue_finCast
    {N n m : Nat} (h : n = m) (c : Real) (p : Fin n → Real)
    (ell : Fin n) :
    sixVertexZeroPhaseBetheEigenvalueValue c N
        (fun i : Fin m => p (Fin.cast h.symm i)) (Fin.cast h ell) =
      sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  subst m
  simp

theorem sixVertexFixedOddChargeCentralIndex_cast
    (s k : Nat) :
    Fin.cast (sixVertexFixedOddChargeBetheParticleCount_eq s k)
        (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) =
      sixVertexOddCentralIndex (s + k + 1) := by
  apply Fin.ext
  simp [sixVertexFixedChargeBetheCentralIndex,
    sixVertexOddCentralIndex]
  omega

end
end StatMech.FrontierD
