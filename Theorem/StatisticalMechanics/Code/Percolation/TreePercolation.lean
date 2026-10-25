/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Percolation.TreePercolation
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

@[simp] lemma treeGF_one (b : ℕ) (p : ℝ) : treeGF b p 1 = 1 := by simp [treeGF]

lemma treeGF_continuous (b : ℕ) (p : ℝ) : Continuous (treeGF b p) := by
  unfold treeGF; fun_prop


lemma treeGF_eq_pgf (b : ℕ) (p s : ℝ) :
    treeGF b p s = ∑ k ∈ range (b + 1), binomialOffspringPMF b p k * s ^ k := by
  unfold treeGF binomialOffspringPMF
  have hcomm : (1 - p + p * s) = (p * s + (1 - p)) := by ring
  rw [hcomm, add_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_pow]; ring


lemma binomialOffspringPMF_sum (b : ℕ) (p : ℝ) :
    ∑ k ∈ range (b + 1), binomialOffspringPMF b p k = 1 := by
  have h := treeGF_eq_pgf b p 1
  simp only [treeGF_one, one_pow, mul_one] at h
  exact h.symm


lemma treeGF_hasDerivAt (b : ℕ) (p s : ℝ) :
    HasDerivAt (treeGF b p) ((b : ℝ) * (1 - p + p * s) ^ (b - 1) * p) s := by
  have hu : HasDerivAt (fun s => 1 - p + p * s) p s := by
    convert ((hasDerivAt_id s).const_mul p).const_add (1 - p) using 1
    · ext x
      simp [id]
    · ring
  convert hu.pow b using 1
  ext s
  simp [treeGF, Pi.pow_apply]


lemma treeGF_hasDerivAt_one (b : ℕ) (p : ℝ) :
    HasDerivAt (treeGF b p) ((b : ℝ) * p) 1 := by
  have h := treeGF_hasDerivAt b p 1
  have heq : (b : ℝ) * (1 - p + p * 1) ^ (b - 1) * p = (b : ℝ) * p := by ring_nf
  rwa [heq] at h


end Percolation
end StatMech
