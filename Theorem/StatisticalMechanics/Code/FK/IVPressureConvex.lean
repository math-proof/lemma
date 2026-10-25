/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem ivp2_expmul_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by simpa using (hasDerivAt_id t).const_mul c
  have := (Real.hasDerivAt_exp (c * t)).comp t h1
  simpa [mul_comm] using this

variable {ι : Type*} [Fintype ι]


theorem ivp2_sumExp_hasDerivAt (b a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, b i * Real.exp (a i * s))
      (∑ i, b i * a i * Real.exp (a i * t)) t := by
  have key : HasDerivAt (∑ i : ι, fun s => b i * Real.exp (a i * s))
      (∑ i, b i * (a i * Real.exp (a i * t))) t :=
    HasDerivAt.sum (fun i _ => (ivp2_expmul_hasDerivAt (a i) t).const_mul (b i))
  have hfun : (∑ i : ι, fun s => b i * Real.exp (a i * s))
      = fun s => ∑ i, b i * Real.exp (a i * s) := by funext s; rw [Finset.sum_apply]
  rw [hfun] at key
  have heq : (∑ i, b i * (a i * Real.exp (a i * t)))
      = ∑ i, b i * a i * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [heq] at key; exact key


end FK
end StatMech
