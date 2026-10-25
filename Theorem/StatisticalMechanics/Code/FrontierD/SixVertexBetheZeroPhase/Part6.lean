/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem norm_sixVertexZeroPhaseBetheEigenvalueCandidate
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    ‖sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell‖ =
      sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  have hpref := sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell
  unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBetheEigenvalueValue
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpref,
    norm_prod]

theorem sixVertexZeroPhaseBetheEigenvalueValue_pos
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    0 < sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  unfold sixVertexZeroPhaseBetheEigenvalueValue
  apply mul_pos (sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell)
  apply Finset.prod_pos
  intro j hj
  exact norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc (p j))

theorem sixVertexZeroPhaseBetheEigenvalueValue_log
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    Real.log (sixVertexZeroPhaseBetheEigenvalueValue c N p ell) =
      Real.log (sixVertexZeroPhaseBethePrefactor c N p ell) +
        ∑ j ∈ (Finset.univ.erase ell),
          Real.log ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ := by
  have hpref := sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell
  have hnorm (j : Fin n) :
      ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sixVertexBetheM_phase_ne_zero hc (p j))
  unfold sixVertexZeroPhaseBetheEigenvalueValue
  rw [Real.log_mul hpref.ne' (Finset.prod_ne_zero_iff.mpr
    (fun j hj => hnorm j)), Real.log_prod]
  exact fun j hj => hnorm j


end
end StatMech.FrontierD
