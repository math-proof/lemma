/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.MaxElementDecomp.Part3
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]


theorem mxd_fiberWeight_nonneg [Nonempty ι] (p : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) :
    0 ≤ mxd_fiberWeight p φ e := by
  unfold mxd_fiberWeight
  exact Finset.sum_nonneg (fun S _ => sq_nonneg _)


theorem mxd_var_decomp [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      = ∑ e : ι, mxd_fiberWeight p φ e := by
  rw [ptn_var_eq_fourierWeight hp0 hp1]
  unfold mxd_fiberWeight mxd_fiber
  
  rw [Finset.sum_fiberwise (univ.erase (∅ : Finset ι)) mxd_maxE
      (fun S => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)]


end StatMech.Probability
