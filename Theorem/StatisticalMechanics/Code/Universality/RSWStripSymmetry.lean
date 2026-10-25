/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Def.StatisticalMechanics.Code.Universality.RSWStripSymmetry
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


@[simp] theorem rss_stripReflect_zero (n : ℤ) (x : Site 2) :
    rss_stripReflect n x 0 = x 0 + 1 := by
  rfl

@[simp] theorem rss_stripReflect_one (n : ℤ) (x : Site 2) :
    rss_stripReflect n x 1 = 2 * n - 1 - x 1 := by
  rfl

@[simp] theorem rss_stripReflect_symm_zero (n : ℤ) (x : Site 2) :
    (rss_stripReflect n).symm x 0 = x 0 - 1 := by
  rfl

@[simp] theorem rss_stripReflect_symm_one (n : ℤ) (x : Site 2) :
    (rss_stripReflect n).symm x 1 = 2 * n - 1 - x 1 := by
  rfl


theorem rss_adj_stripReflect (n : ℤ) (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rss_stripReflect n x) (rss_stripReflect n y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rss_stripReflect_zero, rss_stripReflect_one]
  rw [show (x 0 + 1) - (y 0 + 1) = x 0 - y 0 by ring,
    show (2 * n - 1 - x 1) - (2 * n - 1 - y 1) = -(x 1 - y 1) by ring,
    Int.natAbs_neg]


end Universality
end StatMech
