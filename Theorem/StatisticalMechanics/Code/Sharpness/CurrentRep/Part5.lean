/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Def.StatisticalMechanics.Code.Sharpness.CurrentRep.Part4
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem boltzmannJ_pos (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    0 < boltzmannJ G β J s := Real.exp_pos _


theorem partitionJ_pos (β : ℝ) (J : Sym2 V → ℝ) : 0 < partitionJ G β J :=
  Finset.sum_pos (fun s _ => boltzmannJ_pos G β J s) Finset.univ_nonempty


theorem partitionJ_eq_currentSum (β : ℝ) (J : Sym2 V → ℝ) :
    partitionJ G β J = (2 : ℝ) ^ (Fintype.card V) * currentSum G β J ∅ := by
  unfold partitionJ
  rw [show (∑ s : ConfigSpace V, boltzmannJ G β J s)
        = ∑ s : ConfigSpace V, spinProd (∅ : Finset V) s * boltzmannJ G β J s from
      Finset.sum_congr rfl (fun s _ => by rw [spinProd_empty, one_mul])]
  exact spinSum_eq_currentSum G β J ∅


theorem current_representation (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G β J A = currentSum G β J A / currentSum G β J ∅ := by
  unfold expectationJ
  rw [spinSum_eq_currentSum, partitionJ_eq_currentSum]
  have h2 : (2 : ℝ) ^ (Fintype.card V) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ h2]


theorem boltzmannJ_one_eq_isingWeight (β : ℝ) (s : ConfigSpace V) :
    boltzmannJ G β (fun _ => 1) s = isingWeight G β 0 s := by
  unfold boltzmannJ isingWeight hamiltonian
  congr 1
  simp only [zero_mul, sub_zero, one_mul]
  ring


theorem partitionJ_one_eq_isingZ (β : ℝ) :
    partitionJ G β (fun _ => 1) = isingZ G β 0 := by
  unfold partitionJ isingZ
  exact Finset.sum_congr rfl (fun s _ => boltzmannJ_one_eq_isingWeight G β s)


theorem expectationJ_one_eq_isingExpectation (β : ℝ) (A : Finset V) :
    expectationJ G β (fun _ => 1) A = isingExpectation G β 0 (spinProd A) := by
  unfold expectationJ isingExpectation isingProb
  rw [partitionJ_one_eq_isingZ, Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [boltzmannJ_one_eq_isingWeight, div_mul_eq_mul_div, mul_comm]


theorem isingExpectation_eq_currentSum_ratio (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
      = currentSum G β (fun _ => 1) A / currentSum G β (fun _ => 1) ∅ := by
  rw [← expectationJ_one_eq_isingExpectation, current_representation]

end Sharpness
end StatMech
