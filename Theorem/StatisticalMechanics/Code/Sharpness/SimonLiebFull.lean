/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.SimonLiebFull
open SimpleGraph Finset
open scoped BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ssl_summable_classTerm (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      if sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
        then weight G β J (ofEdgeFun G m) else 0) := by
  refine Summable.of_norm ((summable_norm_weight_ofEdgeFun G β J).of_nonneg_of_le
    (fun m => norm_nonneg _) (fun m => ?_))
  by_cases h : sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
  · rw [if_pos h]
  · rw [if_neg h]; simp


theorem ssl_sum_backboneClassSum (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} [Fintype ι] (sel : (↥G.edgeFinset → ℕ) → ι) :
    ∑ i : ι, ssl_backboneClassSum G β J x y sel i = currentSum G β J {x, y} := by
  classical
  unfold ssl_backboneClassSum currentSum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset ι))
        (fun i _ => ssl_summable_classTerm G β J x y sel i)]
  refine tsum_congr (fun m => ?_)
  by_cases hsrc : sources G (ofEdgeFun G m) = {x, y}
  · rw [if_pos hsrc, Finset.sum_eq_single (sel m)]
    · rw [if_pos ⟨hsrc, rfl⟩]
    · intro j _ hj; rw [if_neg]; rintro ⟨_, h2⟩; exact hj h2.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hsrc]
    exact Finset.sum_eq_zero (fun j _ => by rw [if_neg]; rintro ⟨h1, _⟩; exact hsrc h1)


end Sharpness
end StatMech
