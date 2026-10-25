/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Def.StatisticalMechanics.Code.Universality.CrossingReflection
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


@[simp] theorem crf_swap_zero (x : Site 2) : (crf_swap x) 0 = x 1 := by
  simp [crf_swap, crf_swapFun]

@[simp] theorem crf_swap_one (x : Site 2) : (crf_swap x) 1 = x 0 := by
  simp [crf_swap, crf_swapFun]

@[simp] theorem crf_swap_symm : crf_swap.symm = crf_swap := rfl

@[simp] theorem crf_swap_involutive (x : Site 2) : crf_swap (crf_swap x) = x := by
  funext i; fin_cases i <;> simp


theorem crf_adj_swap (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (crf_swap x) (crf_swap y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [crf_swap_zero, crf_swap_one]
  constructor <;> intro h <;> omega


end Universality
end StatMech
