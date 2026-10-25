/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Def.StatisticalMechanics.Code.Walls.bc59corridors.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc59_originTrifModification_of_hasCorridors {n : ℕ}
    (h : bc59_HasDisjointCorridors d n) : bc58_OriginTrifModification d n := by
  intro ω hω
  exact bc59_corridors_give_trifurcation ω (h ω hω)


theorem bc59_burton_keane_bernoulli_of_hasCorridors (hd : 1 ≤ d)
    (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (h : ∀ n : ℕ, bc59_HasDisjointCorridors d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc58_burton_keane_bernoulli_of_originTrifModification hd p hp1 hp0
    (fun n => bc59_originTrifModification_of_hasCorridors (h n))


end StatMech.Walls
