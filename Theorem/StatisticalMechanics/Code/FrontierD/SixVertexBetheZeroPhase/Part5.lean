/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCoordinateBetheZeroPhaseEigenrelation_one
    {N : Nat} (c : Real) (p : Fin 1 -> Real) (hp : p 0 = 0) :
    SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p 0 := by
  classical
  let e := sixVertexOneSectorEquiv N
  unfold SixVertexCoordinateBetheZeroPhaseEigenrelation
  funext x
  rw [sixVertexSectorTransferComplex_mulVec_apply]
  have heval (y : SixVertexSector N 1) :
      e y = sixVertexSectorPosition y 0 := rfl
  have hreindex :
      (∑ y, (sixVertexSectorTransfer N 1 c x y : Complex) *
          sixVertexCoordinateBetheWave c p y) =
        ∑ i : Fin N, if e x = i then (2 : Complex) else (c : Complex) ^ 2 := by
    apply Fintype.sum_equiv e
    intro y
    rw [sixVertexSectorTransfer_one_apply,
      sixVertexCoordinateBetheWave_one, hp]
    simp only [sixVertexBethePhase, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_pow, mul_one]
    by_cases hxy : x = y
    · subst y
      simp [heval]
    · have hpos : sixVertexSectorPosition x 0 ≠
          sixVertexSectorPosition y 0 := by
        intro h
        apply hxy
        apply e.injective
        simpa [heval] using h
      simp [hxy, hpos, heval]
  rw [hreindex]
  have hsum :
      (∑ i : Fin N, if e x = i then (2 : Complex) else (c : Complex) ^ 2) =
        2 + (N - 1 : Nat) * (c : Complex) ^ 2 := by
    by_cases hN : N = 0
    · subst N
      exact Fin.elim0 (e x)
    · have hrewrite :
          (∑ i : Fin N, if e x = i then (2 : Complex) else (c : Complex) ^ 2) =
            ∑ i : Fin N,
              ((if e x = i then 2 - (c : Complex) ^ 2 else 0) +
                (c : Complex) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hxi : e x = i <;> simp [hxi]
      rw [hrewrite, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN)]
      push_cast
      ring
  rw [hsum]
  simp only [Pi.smul_apply, sixVertexCoordinateBetheWave_one, hp,
    sixVertexBethePhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_pow, smul_eq_mul, mul_one]
  unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBethePrefactor
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.erase_singleton, Finset.sum_empty, mul_zero, add_zero,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_one, Finset.prod_empty, mul_one, add_right_inj]
  have hNpos : 0 < N := by
    have := (sixVertexSectorPosition x 0).isLt
    omega
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hNpos.ne')]
  push_cast
  ring


end
end StatMech.FrontierD
