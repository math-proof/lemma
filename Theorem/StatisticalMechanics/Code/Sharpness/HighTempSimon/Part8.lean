/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part10
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem twoPointJ_simonLieb_finite (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o : V) (ho : o ∈ S) :
    SimonLieb (twoPointJ G beta J) o S
      (simonWeightPair G beta J S o) (Finset.univ \ S) := by
  apply simonLieb_of_firstExit
  · exact fun a b => twoPointJ_nonneg G beta J hbeta hJ a b
  · intro x y
    unfold simonWeightPair
    apply mul_nonneg
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hbeta (hJ s(x, y))))
        (Real.cosh_pos _).le
    · apply twoPointJ_nonneg G beta (couplingIn J S) hbeta
      intro e
      unfold couplingIn
      split <;> simp_all [hJ e]
  · intro z hz
    simpa only [simonWeightPair] using
      twoPointJ_simon_finite G beta J hbeta hJ S o z ho hz

end Sharpness
end StatMech
