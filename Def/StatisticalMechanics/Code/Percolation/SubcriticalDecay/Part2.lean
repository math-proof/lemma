module
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay
open MeasureTheory Set
open scoped NNReal ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def crossProb (d : ℕ) (p : NNReal) (hp : p ≤ 1) (n : ℕ) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEvent d n)


end Percolation
end StatMech
