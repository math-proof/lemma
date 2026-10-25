/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinAssembly
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
import Def.StatisticalMechanics.Code.Onsager.SpinPolynomial


namespace StatMech.Onsager

open StatMech.Ising Polynomial

theorem eval_ons_sectorPoly (L : ℕ) [Fact (2 < L)] (x : ℝ) (h : Fin 2 × Fin 2) :
    eval x (ons_sectorPoly L h) = ons_sectorWeight L x h := by
  unfold ons_sectorPoly ons_sectorWeight
  simp_rw [Polynomial.eval_finset_sum, eval_pow, eval_X]

theorem eval_ons_spinPoly00 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly00 L) = ons_spin00 L x := by
  simp [ons_spinPoly00, ons_spin00, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]

theorem eval_ons_spinPoly10 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly10 L) = ons_spin10 L x := by
  simp [ons_spinPoly10, ons_spin10, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]

theorem eval_ons_spinPoly01 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly01 L) = ons_spin01 L x := by
  simp [ons_spinPoly01, ons_spin01, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]

theorem eval_ons_spinPoly11 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly11 L) = ons_spin11 L x := by
  simp [ons_spinPoly11, ons_spin11, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]


end StatMech.Onsager
