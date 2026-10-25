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
import Def.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part3


namespace StatMech.Onsager

open StatMech.Ising Polynomial

theorem eval_ons_spinDetPoly (L : ℕ) (x : ℝ) (a b : Fin 2) :
    eval x (ons_spinDetPoly L a b) = ons_spinDetX L x a b := by
  unfold ons_spinDetPoly ons_spinDetX
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp
  ring

end StatMech.Onsager
