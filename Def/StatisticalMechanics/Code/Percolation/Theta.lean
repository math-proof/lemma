/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Theta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


def origin (d : ℕ) : Site d := fun _ => 0


def percolationEvent (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (StatMech.Lattice.cluster d ω (origin d)).Infinite}


noncomputable def theta (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (percolationEvent d)


def subcriticalSet (d : ℕ) : Set ℝ≥0 :=
  {p : ℝ≥0 | ∃ hp : p ≤ 1, theta d p hp = 0}


noncomputable def pc (d : ℕ) : ℝ≥0 :=
  sSup (subcriticalSet d)

end Percolation
end StatMech
