/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc31globalarm.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc32forestsep.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc33_rayWalk {V : Type*} (G : SimpleGraph V) (r : ℕ → V)
    (hadj : ∀ k, G.Adj (r k) (r (k + 1))) : ∀ j, G.Walk (r 0) (r j)
  | 0 => Walk.nil
  | (i+1) => (bc33_rayWalk G r hadj i).concat (hadj i)


end StatMech.Walls
